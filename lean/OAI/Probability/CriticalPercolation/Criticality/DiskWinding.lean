import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.DiskWinding

def increment (a b : Real.Angle) : ℝ := (b-a).toReal

lemma increment_add_of_short {a b c : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) :
    increment a b+increment b c=increment a c := by
  let z := increment a b+increment b c-increment a c
  have hco : (z : Real.Angle)=0 := by
    simp only [z,increment,Real.Angle.coe_sub,Real.Angle.coe_add,Real.Angle.coe_toReal]
    abel
  have hbounded : -Real.pi<z ∧ z≤Real.pi := by
    obtain ⟨habl,habu⟩ := abs_lt.mp hab
    obtain ⟨hbcl,hbcu⟩ := abs_lt.mp hbc
    obtain ⟨hacl,hacu⟩ := abs_lt.mp hac
    dsimp [z]
    constructor <;> linarith [Real.pi_pos]
  have hz := Real.Angle.toReal_coe_eq_self_iff.mpr hbounded
  rw [hco,Real.Angle.toReal_zero] at hz
  dsimp [z] at hz
  linarith

lemma sum_successive_sub (f : ℕ → ℝ) (K : ℕ) :
    ∑ k∈Finset.range K, (f (k+1)-f k)=f K-f 0 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; ring

lemma cell_balance {a b c d : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) (had : |increment a d|<Real.pi/4)
    (hdc : |increment d c|<Real.pi/4) :
    increment a b+increment b c=increment a d+increment d c :=
  (increment_add_of_short hab hbc hac).trans (increment_add_of_short had hdc hac).symm

theorem boundary_sum_zero (F : ℕ → ℕ → Real.Angle) (N K : ℕ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hhoriz : ∀ i≤N, ∀ k<K, |increment (F i k) (F i (k+1))|<Real.pi/4)
    (hvert : ∀ i<N, ∀ k≤K, |increment (F i k) (F (i+1) k)|<Real.pi/4)
    (hdiag : ∀ i<N, ∀ k<K, |increment (F i k) (F (i+1) (k+1))|<Real.pi/4) :
    ∑ k∈Finset.range K, increment (F N k) (F N (k+1))=0 := by
  have step : ∀ i<N,
      (∑ k∈Finset.range K, increment (F (i+1) k) (F (i+1) (k+1)))=
      ∑ k∈Finset.range K, increment (F i k) (F i (k+1)) := by
    intro i hi
    let v : ℕ → ℝ := fun k => increment (F i k) (F (i+1) k)
    have hver : ∑ k∈Finset.range K, (v (k+1)-v k)=0 := by
      rw [sum_successive_sub]
      dsimp [v]
      rw [hseam i (by omega),hseam (i+1) (by omega),sub_self]
    have heach : ∀ k∈Finset.range K,
        increment (F (i+1) k) (F (i+1) (k+1))=
        increment (F i k) (F i (k+1))+(v (k+1)-v k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h := cell_balance (hhoriz i (by omega) k hk')
        (hvert i hi (k+1) (by omega)) (hdiag i hi k hk')
        (hvert i hi k (by omega)) (hhoriz (i+1) (by omega) k hk')
      dsimp [v]
      linarith
    rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib,hver,add_zero]
  have all : ∀ i≤N, ∑ k∈Finset.range K, increment (F i k) (F i (k+1))=0 := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcenter k (by have := Finset.mem_range.mp hk; omega),
        hcenter (k+1) (by have := Finset.mem_range.mp hk; omega)]
      simp [increment]
    | succ i ih =>
      intro hi
      rw [step i (by omega),ih (by omega)]
  exact all N le_rfl

lemma boundary_sum_lift (F : ℕ → Real.Angle) (b : ℕ → ℝ) (K : ℕ)
    (hlift : ∀ k≤K, F k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi) :
    ∑ k∈Finset.range K, increment (F k) (F (k+1))=b K-b 0 := by
  rw [←sum_successive_sub b K]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [increment,hlift k (by omega),hlift (k+1) (by omega),←Real.Angle.coe_sub]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨(abs_lt.mp (hstep k hk')).1,
    (abs_lt.mp (hstep k hk')).2.le⟩

theorem exists_large_edge (F : ℕ → ℕ → Real.Angle) (N K : ℕ) (b : ℕ → ℝ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hlift : ∀ k≤K, F N k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi)
    (hturn : b K-b 0=2*Real.pi) :
    (∃ i≤N, ∃ k<K, Real.pi/4≤|increment (F i k) (F i (k+1))|) ∨
    (∃ i<N, ∃ k≤K, Real.pi/4≤|increment (F i k) (F (i+1) k)|) ∨
    (∃ i<N, ∃ k<K, Real.pi/4≤|increment (F i k) (F (i+1) (k+1))|) := by
  by_contra hn
  push Not at hn
  have hz := boundary_sum_zero F N K hcenter hseam hn.1 hn.2.1 hn.2.2
  have ht := boundary_sum_lift (F N) b K hlift hstep
  rw [hz,hturn] at ht
  linarith [Real.pi_pos]

lemma boundary_mesh_lifts (φ e : ℕ → ℝ) (K : ℕ)
    (hmesh : ∀ k<K, |φ (k+1)-φ k|<Real.pi/32)
    (herr : ∀ k≤K, |e k|<Real.pi/8) :
    ∀ k<K, |(2*φ (k+1)+Real.pi+e (k+1))-(2*φ k+Real.pi+e k)|<Real.pi := by
  intro k hk
  obtain ⟨hma,hmb⟩ := abs_lt.mp (hmesh k hk)
  obtain ⟨hea,heb⟩ := abs_lt.mp (herr k (by omega))
  obtain ⟨hfa,hfb⟩ := abs_lt.mp (herr (k+1) (by omega))
  apply abs_lt.mpr
  constructor <;> linarith [Real.pi_pos]

end CriticalPercolation.DiskWinding
end
end
end

end OAI
