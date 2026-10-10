import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory

def torusQuadratic (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) : ℝ :=
  s 0*(h 0 : ℝ)^2+2*s 1*(h 0 : ℝ)*(h 1 : ℝ)+s 2*(h 1 : ℝ)^2

lemma real_outer_pair_injective {a b c d : ℝ}
    (h0 : a^2=c^2) (h1 : b^2=d^2) (h2 : a*b=c*d) :
    (a=c ∧ b=d) ∨ (a= -c ∧ b= -d) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h0 with h0|h0 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h1|h1
  · exact Or.inl ⟨h0,h1⟩
  · by_cases hc : c=0
    · right; constructor <;> linarith
    · left; refine ⟨h0,?_⟩
      have hz : c*(b-d)=0 := by rw [h0] at h2; nlinarith
      have := (mul_eq_zero.mp hz).resolve_left hc
      linarith
  · by_cases hd : d=0
    · right; constructor <;> linarith
    · left; refine ⟨?_,h1⟩
      have hz : (a-c)*d=0 := by rw [h1] at h2; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right hd
      linarith
  · exact Or.inr ⟨h0,h1⟩

def torusResonanceForm (h l : Fin 2 → ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun s := torusQuadratic s h-torusQuadratic s l
  map_add' _ _ := by simp only [torusQuadratic,Pi.add_apply]; ring
  map_smul' _ _ := by simp only [torusQuadratic,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

lemma torusResonance_proper {h l : Fin 2 → ℤ} (he : l ≠ h) (hn : l ≠ -h) :
    (torusResonanceForm h l).ker ≠ ⊤ := by
  intro hk
  have hh (s : Fin 3 → ℝ) : torusQuadratic s h=torusQuadratic s l := by
    have : s∈(torusResonanceForm h l).ker := hk ▸ Submodule.mem_top
    exact sub_eq_zero.mp this
  have h0 := hh ![1,0,0]
  have h1 := hh ![0,0,1]
  have h2 := hh ![0,1,0]
  norm_num [torusQuadratic,Matrix.cons_val_two] at h0 h1 h2
  have h2' : (h 0 : ℝ)*(h 1 : ℝ)=(l 0 : ℝ)*(l 1 : ℝ) := by linarith
  rcases real_outer_pair_injective h0 h1 h2' with hh|hh
  · apply he; ext i; fin_cases i
    · exact_mod_cast hh.1.symm
    · exact_mod_cast hh.2.symm
  · apply hn; ext i; fin_cases i
    · change l 0= -(h 0)
      exact_mod_cast (show (l 0 : ℝ)= -(h 0 : ℝ) by linarith [hh.1])
    · change l 1= -(h 1)
      exact_mod_cast (show (l 1 : ℝ)= -(h 1 : ℝ) by linarith [hh.2])

theorem exists_nonresonant_angular_tensor : ∃ s : Fin 3 → ℝ,
    (∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) ∧
    (∀ h l : Fin 2 → ℤ, torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) := by
  let I := {p : (Fin 2 → ℤ) × (Fin 2 → ℤ) // p.2 ≠ p.1 ∧ p.2 ≠ -p.1}
  let bad : Set (Fin 3 → ℝ) := ⋃ p : I, ((torusResonanceForm p.val.1 p.val.2).ker : Set (Fin 3 → ℝ))
  have hbad : volume bad=0 := by
    apply measure_iUnion_null
    intro p
    exact Measure.addHaar_submodule volume _ (torusResonance_proper p.property.1 p.property.2)
  let o : Fin 3 → ℝ := ![1,0,1]
  obtain ⟨s,hs,hsg⟩ : ∃ s∈Metric.ball o (1/4), s∉bad := by
    by_contra! hn
    have hsub : Metric.ball o (1/4)⊆bad := hn
    have hle := measure_mono (μ := volume) hsub
    rw [hbad] at hle
    exact (Metric.measure_ball_pos volume o (by norm_num : (0:ℝ)<1/4)).not_ge hle
  refine ⟨s,?_,?_⟩
  · have hnorm : ‖s-o‖<1/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hs
    have hi (i : Fin 3) : |s i-o i|<1/4 := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using (norm_le_pi_norm (s-o) i).trans_lt hnorm
    have h0 := (abs_lt.mp (hi 0)).1
    have h1 := abs_lt.mp (hi 1)
    have h2 := (abs_lt.mp (hi 2)).1
    norm_num [o,Matrix.cons_val_two] at h0 h1 h2
    intro x y
    nlinarith [mul_nonneg (show 0 ≤ s 0-3/4 by linarith) (sq_nonneg x),
      mul_nonneg (show 0 ≤ s 2-3/4 by linarith) (sq_nonneg y),
      mul_nonneg (show 0 ≤ 1/4+s 1 by linarith) (sq_nonneg (x+y)),
      mul_nonneg (show 0 ≤ 1/4-s 1 by linarith) (sq_nonneg (x-y))]
  · intro h l hh
    by_contra! hn
    apply hsg
    apply mem_iUnion.mpr
    refine ⟨⟨(h,l),hn⟩,?_⟩
    exact sub_eq_zero.mpr hh

end

open Set

lemma torusQuadratic_sublevel_finite {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) : {h : Fin 2 → ℤ | torusQuadratic s h ≤ R}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (|2*R|+1)
  have hN0 : 0 < (N:ℝ) := lt_trans (by positivity) hN
  apply (Set.Finite.pi' (fun _ : Fin 2 => Set.finite_Icc (-(N:ℤ)) N)).subset
  intro h hh i
  change torusQuadratic s h ≤ R at hh
  have hq := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hq
  have hb : (h i:ℝ)^2 ≤ 2*R := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at *
    · nlinarith [sq_nonneg (h 1:ℝ)]
    · nlinarith [sq_nonneg (h 0:ℝ)]
  have hN2 : 2*R < (N:ℝ)^2 := by
    have habs := le_abs_self (2*R)
    nlinarith [sq_nonneg ((N:ℝ)-1)]
  have hbound : -(N:ℝ) ≤ (h i:ℝ) ∧ (h i:ℝ) ≤ N := by
    constructor
    · nlinarith [sq_nonneg ((h i:ℝ)+(N:ℝ))]
    · nlinarith [sq_nonneg ((h i:ℝ)-(N:ℝ))]
  exact_mod_cast hbound

lemma torusQuadratic_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h : Fin 2 → ℤ} (hh : h≠0) : 0<torusQuadratic s h := by
  have hs' := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hs'
  have hn : (h 0:ℝ)≠0 ∨ (h 1:ℝ)≠0 := by
    by_contra! hc
    apply hh
    have h0 : h 0=0 := by exact_mod_cast hc.1
    have h1 : h 1=0 := by exact_mod_cast hc.2
    ext i; fin_cases i <;> simp [h0,h1]
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (h 1:ℝ)]
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (h 0:ℝ)]

lemma torus_modes_have_first {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) :
    ∃ h∈M, ∀ l∈M, torusQuadratic s h ≤ torusQuadratic s l := by
  obtain ⟨h₀,hh₀⟩ := hne
  let K := M∩{h | torusQuadratic s h ≤ torusQuadratic s h₀}
  have hK : K.Finite := (torusQuadratic_sublevel_finite hs _).subset inter_subset_right
  obtain ⟨h,hh,hmin⟩ := Set.exists_min_image K (torusQuadratic s) hK ⟨h₀,hh₀,show torusQuadratic s h₀ ≤ torusQuadratic s h₀ from le_rfl⟩
  refine ⟨h,hh.1,fun l hl => ?_⟩
  by_cases hll : torusQuadratic s l ≤ torusQuadratic s h₀
  · exact hmin l ⟨hl,hll⟩
  · exact hh.2.trans (le_of_not_ge hll)

theorem torus_leading_pair_gap {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ, torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    {M : Set (Fin 2 → ℤ)} (hne : M.Nonempty) (hzero : 0∉M) :
    ∃ h∈M, 0<torusQuadratic s h ∧ ∃ δ : ℝ, 0<δ ∧
      ∀ l∈M, l≠h → l≠-h → torusQuadratic s h+δ ≤ torusQuadratic s l := by
  obtain ⟨h,hh,hmin⟩ := torus_modes_have_first hs hne
  refine ⟨h,hh,torusQuadratic_pos hs (fun he => hzero (he ▸ hh)),?_⟩
  let N := {l∈M | l≠h ∧ l≠-h}
  by_cases hN : N.Nonempty
  · obtain ⟨g,hg,hgmin⟩ := torus_modes_have_first hs hN
    have hlt : torusQuadratic s h<torusQuadratic s g := by
      apply lt_of_le_of_ne (hmin g hg.1)
      intro he
      exact (hres h g he).elim hg.2.1 hg.2.2
    refine ⟨torusQuadratic s g-torusQuadratic s h,sub_pos.mpr hlt,?_⟩
    intro l hl hle hln
    have hi := hgmin l ⟨hl,hle,hln⟩
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro l hl hle hln
    exact False.elim (hN ⟨l,hl,hle,hln⟩)

end ScalarConductivity

end

end OAI
