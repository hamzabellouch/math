import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.SemigroupComparisonArithmetic
import OAI.Analysis.JiangSu.CuntzSemigroup.SemigroupStates
import OAI.Analysis.JiangSu.CuntzSemigroup.SemigroupGrothendieck

namespace OAI


noncomputable section
namespace Pureness
namespace RationalRiesz
open Set Submodule

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

theorem exists_normalized_positive (C : PointedCone ℚ E) (u : E)
    (hu : -u ∉ C) (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C) :
    ∃ f : E →ₗ[ℚ] ℝ, f u = 1 ∧ ∀ z ∈ C, 0 ≤ f z := by
  have hu0 : u ≠ 0 := by intro hzero; apply hu; simp [hzero]
  let p : E →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton u 1 hu0
  have hp : ∀ z : p.domain, (z : E) ∈ C → 0 ≤ p z := by
    rintro ⟨z,hz⟩ hzc
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, Rat.smul_def, mul_one]
    have hr : 0 ≤ r := by
      by_contra h
      have hr : r < 0 := lt_of_not_ge h
      apply hu
      have hmem := C.smul_mem (show 0 ≤ -r⁻¹ by exact neg_nonneg.mpr (inv_nonpos.mpr hr.le)) hzc
      simpa only [smul_smul, neg_mul, inv_mul_cancel₀ hr.ne, neg_smul, one_smul] using hmem
    exact_mod_cast hr
  have hd : ∀ z : E, ∃ x : p.domain, (x : E) + z ∈ C := by
    intro z
    obtain ⟨r,hr⟩ := hbound z
    exact ⟨⟨r • u, Submodule.mem_span_singleton.mpr ⟨r,rfl⟩⟩,hr⟩
  obtain ⟨f,hf,hpos⟩ := riesz_extension C p hp hd
  refine ⟨f, ?_, hpos⟩
  have h := hf ⟨u, Submodule.mem_span_singleton_self u⟩
  exact h.trans (LinearPMap.mkSpanSingleton_apply ℚ ℚ hu0 1)

def adjoinNegative (C : PointedCone ℚ E) (v : E) : PointedCone ℚ E where
  carrier := {z | ∃ c ∈ C, ∃ t : ℚ, 0 ≤ t ∧ z = c - t • v}
  zero_mem' := ⟨0,C.zero_mem,0,le_rfl,by simp⟩
  add_mem' := by
    rintro a b ⟨c,hc,t,ht,rfl⟩ ⟨d,hd,s,hs,rfl⟩
    exact ⟨c+d,C.add_mem hc hd,t+s,add_nonneg ht hs,by simp [add_smul]; abel⟩
  smul_mem' := by
    rintro ⟨r,hr⟩ z ⟨c,hc,t,ht,rfl⟩
    exact ⟨r • c,C.smul_mem hr hc,r*t,mul_nonneg hr ht,by simp [smul_sub,smul_smul]⟩

lemma mem_adjoinNegative (C : PointedCone ℚ E) (v z : E) (hz : z ∈ C) :
    z ∈ adjoinNegative C v := ⟨z,hz,0,le_rfl,by simp⟩

theorem separating_state (C : PointedCone ℚ E) (u x : E) (hu : u ∈ C)
    (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C)
    (hfail : ∀ q : ℚ, q < 1 → q • u - x ∉ C) :
    ∃ f : E →ₗ[ℚ] ℝ, f u = 1 ∧ (∀ z ∈ C, 0 ≤ f z) ∧ 1 ≤ f x := by
  let D := adjoinNegative C (u-x)
  have hproper : -u ∉ D := by
    rintro ⟨c,hc,t,ht,heq⟩
    by_cases ht0 : t = 0
    · have hc' : -u ∈ C := by
        have heq0 : -u = c := by simpa [ht0] using heq
        exact heq0.symm ▸ hc
      obtain ⟨r,hr⟩ := hbound (-x)
      have hr' : -r • u ∈ C := by
        by_cases hr0 : 0 ≤ r
        · simpa only [smul_neg, neg_smul] using C.smul_mem hr0 hc'
        · exact C.smul_mem (neg_nonneg.mpr (le_of_not_ge hr0)) hu
      have hsum := C.add_mem hr hr'
      apply hfail 0 (by norm_num)
      simpa [neg_smul] using hsum
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hcform : c = (t-1) • u - t • x := by
        have : c = -u + t • (u-x) := (eq_sub_iff_add_eq.mp heq).symm
        rw [this, smul_sub, sub_smul, one_smul]
        abel
      have hmem := C.smul_mem (inv_nonneg.mpr ht) hc
      have heq' : t⁻¹ • c = (1-t⁻¹) • u - x := by
        rw [hcform, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        congr 2
        rw [mul_sub, inv_mul_cancel₀ ht0, mul_one]
      rw [heq'] at hmem
      exact hfail (1-t⁻¹) (by linarith [inv_pos.mpr htpos]) hmem
  obtain ⟨f,hfu,hf⟩ := exists_normalized_positive D u hproper
    (fun z => let ⟨r,hr⟩ := hbound z; ⟨r,mem_adjoinNegative C (u-x) _ hr⟩)
  refine ⟨f,hfu,fun z hz => hf z (mem_adjoinNegative C (u-x) z hz),?_⟩
  have hneg : -(u-x) ∈ D := ⟨0,C.zero_mem,1,by norm_num,by simp⟩
  have h := hf _ hneg
  rw [map_neg,map_sub,hfu] at h
  linarith

theorem strict_bound_of_states (C : PointedCone ℚ E) (u x : E) (hu : u ∈ C)
    (hbound : ∀ z : E, ∃ r : ℚ, r • u + z ∈ C)
    (hgap : ∀ f : E →ₗ[ℚ] ℝ, f u = 1 → (∀ z ∈ C, 0 ≤ f z) → f x < 1) :
    ∃ q : ℚ, q < 1 ∧ q • u - x ∈ C := by
  by_contra h
  push Not at h
  obtain ⟨f,hfu,hf,hfx⟩ := separating_state C u x hu hbound h
  exact (not_lt_of_ge hfx) (hgap f hfu hf)

end RationalRiesz
end Pureness


namespace Pureness.OrderedSemigroup
variable {G : Type*} [AddCommGroup G]

lemma rational_nat_mul (q : ℚ) (hq : 0 ≤ q) :
    (q.den : ℚ) * q = (q.num.toNat : ℚ) := by
  have hp : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  calc
    (q.den : ℚ) * q = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
      congrArg (fun t : ℚ => (q.den : ℚ)*t) (Rat.num_div_den q).symm
    _ = (q.num : ℚ) := mul_div_cancel₀ _ hd
    _ = (q.num.toNat : ℚ) := by exact_mod_cast hp.symm

def rationalCone (P : AddSubmonoid G) : PointedCone ℚ (RationalGroup G) where
  carrier := {z | ∃ n : ℕ, 0 < n ∧ ∃ g ∈ P, n • z = toRationalGroup G g}
  zero_mem' := ⟨1,by omega,0,P.zero_mem,by simp⟩
  add_mem' := by
    rintro z w ⟨n,hn,g,hg,hzg⟩ ⟨m,hm,h,hh,hwh⟩
    refine ⟨m*n,Nat.mul_pos hm hn,m • g+n • h,P.add_mem (P.nsmul_mem hg m) (P.nsmul_mem hh n),?_⟩
    calc
      (m*n) • (z+w) = m • (n • z) + n • (m • w) := by
        simp only [nsmul_add, ← mul_nsmul, Nat.mul_comm]
      _ = toRationalGroup G (m • g+n • h) := by rw [hzg,hwh,map_add,map_nsmul,map_nsmul]
  smul_mem' := by
    rintro ⟨q,hq⟩ z ⟨n,hn,g,hg,hzg⟩
    refine ⟨q.den*n,Nat.mul_pos q.den_pos hn,q.num.toNat • g,P.nsmul_mem hg _,?_⟩
    change (q.den*n) • (q • z) = _
    calc
      (q.den*n) • (q • z) = q.num.toNat • (n • z) := by
        simp only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_mul, smul_smul]
        congr 1
        rw [mul_right_comm, rational_nat_mul q hq]
      _ = toRationalGroup G (q.num.toNat • g) := by rw [hzg,map_nsmul]

lemma rationalCone_of_mem (P : AddSubmonoid G) {g : G} (hg : g ∈ P) :
    toRationalGroup G g ∈ rationalCone P := ⟨1,by omega,g,hg,by simp⟩

theorem rationalCone_of_iff (P : AddSubmonoid G) (g : G) :
    toRationalGroup G g ∈ rationalCone P ↔ ∃ n : ℕ, 0 < n ∧ n • g ∈ P := by
  constructor
  · rintro ⟨n,hn,h,hh,he⟩
    rw [← map_nsmul] at he
    obtain ⟨k,hk,hkgh⟩ := (rationalGroup_eq_iff G (n • g) h).mp he
    refine ⟨k*n,Nat.mul_pos hk hn,?_⟩
    rw [Nat.mul_comm k n, mul_nsmul, hkgh]
    exact P.nsmul_mem hh k
  · rintro ⟨n,hn,hg⟩
    exact ⟨n,hn,n • g,hg,(map_nsmul _ n g).symm⟩

theorem rationalCone_orderUnit (P : AddSubmonoid G) (u : G)
    (hbound : ∀ g : G, ∃ n : ℕ, n • u + g ∈ P)
    (z : RationalGroup G) :
    ∃ r : ℚ, r • toRationalGroup G u + z ∈ rationalCone P := by
  obtain ⟨d,hd,g,hg⟩ := rationalGroup_denominator G z
  rw [Nat.cast_smul_eq_nsmul] at hg
  obtain ⟨n,hn⟩ := hbound g
  refine ⟨(n : ℚ)/d,d,hd,n • u+g,hn,?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    d • (((n : ℚ)/(d : ℚ)) • toRationalGroup G u + z) =
        n • toRationalGroup G u + toRationalGroup G g := by
      rw [nsmul_add, hg, ← Nat.cast_smul_eq_nsmul ℚ d, smul_smul]
      rw [mul_div_cancel₀ _ hd0, Nat.cast_smul_eq_nsmul]
    _ = toRationalGroup G (n • u+g) := by rw [map_add,map_nsmul]

end Pureness.OrderedSemigroup


namespace Pureness.OrderedSemigroup
open Algebra
open scoped ENNReal

variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

abbrev semigroupRationalMap : S →+ RationalGroup (GrothendieckAddGroup S) :=
  (toRationalGroup (GrothendieckAddGroup S)).toAddMonoidHom.comp GrothendieckAddGroup.of

abbrev semigroupRationalCone : PointedCone ℚ (RationalGroup (GrothendieckAddGroup S)) :=
  rationalCone (grothendieckCone (S := S))

def stateOfRationalPositive (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : RationalGroup (GrothendieckAddGroup S) →ₗ[ℚ] ℝ)
    (hfu : f (semigroupRationalMap u) = 1)
    (hf : ∀ z ∈ semigroupRationalCone, 0 ≤ f z) : StateSpace u := by
  have hpos : ∀ a : S, 0 ≤ f (semigroupRationalMap a) := fun a =>
    hf _ (rationalCone_of_mem _ (grothendieck_of_nonneg hzero a))
  refine ⟨fun a => ENNReal.ofReal (f (semigroupRationalMap a)), ?_, ?_, ?_, ?_⟩
  · simp
  · intro a b
    simp only [map_add]
    exact ENNReal.ofReal_add (hpos a) (hpos b)
  · intro a b hab
    apply ENNReal.ofReal_le_ofReal
    have h := hf _ (rationalCone_of_mem (grothendieckCone (S := S)) ⟨a,b,hab,rfl⟩)
    simp only [map_sub, sub_nonneg] at h
    dsimp [semigroupRationalMap] at h ⊢
    exact h
  · change ENNReal.ofReal (f (semigroupRationalMap u)) = 1
    rw [hfu, ENNReal.ofReal_one]

theorem exists_strict_buffer_of_states (hzero : ∀ a : S, 0 ≤ a)
    (u x : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (hgap : ∀ f : StateSpace u, f.1 x < 1) :
    ∃ m n : ℕ, m < n ∧ ∃ c : S, n • x+c ≤ m • u+c := by
  let C := semigroupRationalCone (S := S)
  let U := semigroupRationalMap u
  let X := semigroupRationalMap x
  have hU : U ∈ C := rationalCone_of_mem _ (grothendieck_of_nonneg hzero u)
  have hbound : ∀ z, ∃ r : ℚ, r • U+z ∈ C :=
    rationalCone_orderUnit _ _ (grothendieck_orderUnit hzero u hunit)
  obtain ⟨q,hq,hqx⟩ := RationalRiesz.strict_bound_of_states C U X hU hbound (by
    intro f hfu hf
    have h := hgap (stateOfRationalPositive hzero u f hfu hf)
    change ENNReal.ofReal (f X) < 1 at h
    have hh : ENNReal.ofReal (f X) < ENNReal.ofReal 1 := by simpa using h
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hh)
  have hex : ∃ q : ℚ, 0 ≤ q ∧ q < 1 ∧ q • U-X ∈ C := by
    by_cases hq0 : 0 ≤ q
    · exact ⟨q,hq0,hq,hqx⟩
    · refine ⟨0,le_rfl,by norm_num,?_⟩
      have h := C.add_mem (C.smul_mem (neg_nonneg.mpr (le_of_not_ge hq0)) hU) hqx
      have heq : (-q) • U + (q • U-X) = (0 : ℚ) • U-X := by
        rw [neg_smul,zero_smul]
        abel
      exact heq ▸ h
  obtain ⟨q,hq0,hq,hqx⟩ := hex
  let p := q.num.toNat
  let d := q.den
  have hd : 0 < d := q.den_pos
  have hdp : (d : ℚ)*q = p := rational_nat_mul q hq0
  have hpd : p < d := by
    have h := mul_lt_mul_of_pos_left hq (show (0 : ℚ) < d by exact_mod_cast hd)
    rw [hdp,mul_one] at h
    exact_mod_cast h
  have hmem := C.smul_mem (show (0 : ℚ) ≤ d by positivity) hqx
  have heq : (d : ℚ) • (q • U-X) =
      toRationalGroup (GrothendieckAddGroup S)
        (p • GrothendieckAddGroup.of u-d • GrothendieckAddGroup.of x) := by
    rw [smul_sub,smul_smul,hdp,map_sub,map_nsmul,map_nsmul]
    simp only [Nat.cast_smul_eq_nsmul]
    rfl
  rw [heq] at hmem
  obtain ⟨k,hk,hkP⟩ := (rationalCone_of_iff (grothendieckCone (S := S)) _).mp hmem
  have heq2 : k • (p • GrothendieckAddGroup.of u-d • GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of ((k*p) • u)-GrothendieckAddGroup.of ((k*d) • x) := by
    simp only [smul_sub,map_nsmul,mul_nsmul]
    congr 1 <;> exact smul_comm _ _ _
  rw [heq2] at hkP
  obtain ⟨c,hc⟩ := (grothendieck_mem_cone_iff ((k*d) • x) ((k*p) • u)).mp hkP
  exact ⟨k*p,k*d,Nat.mul_lt_mul_of_pos_left hpd hk,c,hc⟩

theorem le_of_states (hzero : ∀ a : S, 0 ≤ a)
    (hAU : ∀ a b : S, ∀ k : ℕ, 1 ≤ k → (k+1) • a ≤ k • b → a ≤ b)
    (u x : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (hgap : ∀ f : StateSpace u, f.1 x < 1) : x ≤ u := by
  obtain ⟨m,n,hmn,c,hc⟩ := exists_strict_buffer_of_states hzero u x hunit hgap
  obtain ⟨k,hk⟩ := hunit c
  exact strict_multiples_le_of_buffer hzero hAU hmn hc hk

end Pureness.OrderedSemigroup
end

end OAI
