import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma val_add_of_zero {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : V.val b = 0) : V.val (a+b) = V.val a := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 < V.val a+1 := by linarith [V.nonneg ha]
    let r := Real.sqrt (ε/(V.val a+1))
    have hr : 0 < r := Real.sqrt_pos.2 (div_pos hε hpos)
    have hrsq : r^2 = ε/(V.val a+1) := Real.sq_sqrt (le_of_lt (div_pos hε hpos))
    have hmul : r^2*(V.val a+1)=ε := by rw [hrsq]; exact div_mul_cancel₀ ε hpos.ne'
    have h := V.weighted_add ha hb r hr.ne'
    rw [hzero,mul_zero,add_zero] at h
    nlinarith [sq_nonneg r]
  · exact V.mono ha (le_add_of_nonneg_right hb)

abbrev IsNull (x : A) : Prop := V.val (star x*x) = 0

lemma null_zero  : IsNull V (0 : A) := by simp [IsNull,V.zero]

lemma null_star {x : A} (hx : IsNull V x) : IsNull V (star x) := by
  simpa only [IsNull,star_star,V.square_swap] using hx

lemma null_add {x y : A} (hx : IsNull V x) (hy : IsNull V y) :
    IsNull V (x+y) := by
  have hab : V.val (star x*x + star y*y) = 0 := by
    rw [val_add_of_zero V (star_mul_self_nonneg x) (star_mul_self_nonneg y) hy]
    exact hx
  have hle : star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x + star y*y) := by
    rw [← sub_nonneg]
    convert star_mul_self_nonneg (x-y) using 1
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  apply le_antisymm _ (V.nonneg (star_mul_self_nonneg _))
  calc V.val (star (x+y)*(x+y)) ≤ V.val ((2:ℝ) • (star x*x + star y*y)) :=
        V.mono (star_mul_self_nonneg _) hle
    _ = 0 := by rw [V.smul,hab,mul_zero]

lemma null_smul {x : A} (hx : IsNull V x) (r : ℂ) :
    IsNull V (r • x) := by
  have h : star (r • x)*(r • x) = Complex.normSq r • (star x*x) := by
    rw [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    change ((starRingEnd ℂ) r * r) • (star x*x) = Complex.normSq r • (star x*x)
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.coe_smul _ _
  dsimp [IsNull]
  rw [h,V.smul,hx,mul_zero]

lemma null_mul_left {x : A} (hx : IsNull V x) (a : A) :
    IsNull V (a*x) := by
  have hle : star (a*x)*(a*x) ≤ ‖a‖^2 • (star x*x) := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) x
    simpa only [star_mul,mul_assoc,Algebra.algebraMap_eq_smul_one,mul_smul_comm,
      smul_mul_assoc,one_mul] using h
  apply le_antisymm _ (V.nonneg (star_mul_self_nonneg _))
  calc V.val (star (a*x)*(a*x)) ≤ V.val (‖a‖^2 • (star x*x)) :=
        V.mono (star_mul_self_nonneg _) hle
    _ = 0 := by rw [V.smul,hx,mul_zero]

lemma null_mul_right {x : A} (hx : IsNull V x) (a : A) :
    IsNull V (x*a) := by
  simpa only [star_mul,star_star] using null_star V (null_mul_left V (null_star V hx) (star a))

lemma continuous_squareVal : Continuous (fun x : A => V.val (star x*x)) := by
  have hl : LipschitzWith 1 (fun x : {a : A // 0≤a} => V.val x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,Subtype.dist_eq,dist_eq_norm,Real.norm_eq_abs] using
      V.lipschitz_positive a.property b.property
  have hc : Continuous (fun x : A => (⟨star x*x,star_mul_self_nonneg x⟩ : {a:A // 0≤a})) :=
    (continuous_star.mul continuous_id).subtype_mk _
  exact hl.continuous.comp hc

def nullIdeal  : ClosedStarIdeal (A) where
  carrier := {x | IsNull V x}
  zero_mem' := null_zero V
  add_mem' := null_add V
  smul_mem' := fun r _ hx => null_smul V hx r
  mul_mem' := fun _ hy => null_mul_left V hy _
  star_mem' := null_star V
  mul_mem_left := fun a _ hx => null_mul_left V hx a
  mul_mem_right := fun _ a hx => null_mul_right V hx a
  closed := isClosed_eq (continuous_squareVal V) continuous_const

lemma val_zero_of_null {a : A} (ha : 0 ≤ a) (hx : IsNull V a) :
    V.val a = 0 := by
  have hs : CFC.sqrt a ∈ (nullIdeal V).toNonUnitalStarSubalgebra := by
    rw [CFC.sqrt_eq_real_sqrt a ha]
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt hx
  change IsNull V (CFC.sqrt a) at hs
  simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self a ha] using hs

lemma null_of_val_zero {a : A} (ha : 0 ≤ a) (hx : V.val a = 0) :
    IsNull V a := by
  have hs : IsNull V (CFC.sqrt a) := by
    simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self a ha] using hx
  simpa only [CFC.sqrt_mul_sqrt_self a ha] using null_mul_left V hs (CFC.sqrt a)

lemma null_posPart {a : A} (hx : IsNull V a) : IsNull V a⁺ := by
  change a⁺ ∈ (nullIdeal V).toNonUnitalStarSubalgebra
  exact cfcₙ_mem (𝕜' := ℂ) (fun t : ℝ => max t 0) hx

lemma null_sub {a b : A} (ha : IsNull V a) (hb : IsNull V b) :
    IsNull V (a-b) := (nullIdeal V).submodule.sub_mem ha hb

lemma val_eq_of_null_sub {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : IsNull V (a-b)) : V.val a = V.val b := by
  have haux {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : IsNull V (a-b)) :
      V.val a ≤ V.val b := by
    have hle : a ≤ b+(a-b)⁺ := by
      have hp := CFC.le_posPart (ha.isSelfAdjoint.sub hb.isSelfAdjoint)
      exact (sub_le_iff_le_add'.1 hp)
    calc V.val a ≤ V.val (b+(a-b)⁺) := V.mono ha hle
      _ = V.val b := val_add_of_zero V hb (CFC.posPart_nonneg _)
        (val_zero_of_null V (CFC.posPart_nonneg _) (null_posPart V hab))
  exact le_antisymm (haux ha hb hab) (haux hb ha (by
    have h := (nullIdeal V).submodule.neg_mem hab
    change IsNull V (-(a-b)) at h
    simpa only [neg_sub] using h))


end KaplanskyConsequences.QuasiValue

end

end OAI
