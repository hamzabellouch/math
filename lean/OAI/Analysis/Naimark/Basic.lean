import Mathlib

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop :=
  Nontrivial A ∧ ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

def IsState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  ‖f‖ = 1 ∧ ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re

def IsFaithfulTracialState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  IsState f ∧ (∀ a b : A, f (a * b) = f (b * a)) ∧
    ∀ a : A, a ≠ 0 → 0 < (f (star a * a)).re

def IsIrreducible {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  π ≠ 0 ∧ ∀ M : Submodule ℂ H, IsClosed (M : Set H) →
    (∀ a : A, ∀ x ∈ M, π a x ∈ M) → M = ⊥ ∨ M = ⊤

def UnitarilyEquivalent {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ a : A, ∀ x : H, U (π a x) = ρ a (U x)

def HasUniqueIrreducibleRepresentation (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
    IsIrreducible π → IsIrreducible ρ → UnitarilyEquivalent π ρ

def IsIsomorphicToCompacts (A : Type u) [CStarAlgebra A]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∃ φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H), Function.Injective φ ∧
    ∀ T : H →L[ℂ] H, (∃ a : A, φ a = T) ↔ IsCompactOperator T

section HNNWords

inductive HNNWord (A : Type*)
  | single : Bool → A → HNNWord A
  | cons : Bool → A → HNNWord A → HNNWord A

namespace HNNWord
variable {A B : Type*} [Mul B]
def first : HNNWord A → Bool
  | .single i _ => i
  | .cons i _ _ => i

def eval (φ : A → B) (v : Bool → B) : HNNWord A → B
  | .single i a => v i * φ a
  | .cons i a w => v i * φ a * w.eval φ v

def Reduced (K : Bool → A → Prop) : HNNWord A → Prop
  | .single _ _ => True
  | .cons i a w => (i = w.first ∨ K i a) ∧ w.Reduced K
end HNNWord

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

def hnnWordSet : Set B := Set.range φ ∪
  {z | ∃ (w : HNNWord A) (a : A), w.Reduced K ∧ z = φ a*w.eval φ v}

def hnnWordSpan : Submodule ℂ B := Submodule.span ℂ (hnnWordSet φ v K)

theorem hnnWordSpan_base (a : A) : φ a ∈ hnnWordSpan φ v K :=
  Submodule.subset_span (Or.inl ⟨a,rfl⟩)

theorem hnnWordSpan_word (w : HNNWord A) (a : A) (hw : w.Reduced K) :
    φ a*w.eval φ v ∈ hnnWordSpan φ v K :=
  Submodule.subset_span (Or.inr ⟨w,a,hw,rfl⟩)

theorem hnnWordSpan_letter (i : Bool) : v i ∈ hnnWordSpan φ v K := by
  simpa only [map_one,one_mul,mul_one,HNNWord.eval] using
    hnnWordSpan_word φ v K (.single i 1) 1 trivial

theorem hnnWordSpan_mul_base (a : A) {x : B} (hx : x ∈ hnnWordSpan φ v K) :
    φ a*x ∈ hnnWordSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨c,rfl⟩ | ⟨w,c,hw,rfl⟩
    · simpa only [← map_mul] using hnnWordSpan_base φ v K (a*c)
    · simpa only [map_mul,mul_assoc] using hnnWordSpan_word φ v K w (a*c) hw
  | zero => simpa only [mul_zero] using (hnnWordSpan φ v K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (hnnWordSpan φ v K).add_mem ix iy
  | smul c x hx ix => simpa only [mul_smul_comm] using (hnnWordSpan φ v K).smul_mem c ix

variable (center r : Bool → A → A)
  (hc : ∀ i a, K i (center i a))
  (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
include hc hr

theorem hnnWordSpan_left_word (i : Bool) (a : A) (w : HNNWord A)
    (hw : w.Reduced K) : v i*(φ a*w.eval φ v) ∈ hnnWordSpan φ v K := by
  by_cases hij : i = w.first
  · have hh := hnnWordSpan_word φ v K (.cons i a w) 1 ⟨Or.inl hij,hw⟩
    simpa only [map_one,one_mul,HNNWord.eval,mul_assoc] using hh
  · have he : w.first = !i := by
      cases i <;> cases h : w.first <;> simp_all
    have hmain := hnnWordSpan_word φ v K (.cons i (center i a) w) 1
      ⟨Or.inr (hc i a),hw⟩
    simp only [map_one,one_mul,HNNWord.eval] at hmain
    cases w with
    | single j d =>
      change j = !i at he
      subst j
      have hh : v i*(φ a*(v (!i)*φ d)) =
          v i*φ (center i a)*(v (!i)*φ d) + φ (r i a*d) := by
        calc
          _ = (v i*φ a*v (!i))*φ d := by simp only [mul_assoc]
          _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
      rw [HNNWord.eval,hh]
      exact (hnnWordSpan φ v K).add_mem hmain (hnnWordSpan_base φ v K _)
    | cons j d tail =>
      change j = !i at he
      subst j
      have hh : v i*(φ a*(v (!i)*φ d*tail.eval φ v)) =
          v i*φ (center i a)*(v (!i)*φ d*tail.eval φ v) +
            φ (r i a*d)*tail.eval φ v := by
        calc
          _ = (v i*φ a*v (!i))*φ d*tail.eval φ v := by simp only [mul_assoc]
          _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
      rw [HNNWord.eval,hh]
      exact (hnnWordSpan φ v K).add_mem hmain (hnnWordSpan_word φ v K tail _ hw.2)

theorem hnnWordSpan_mul_letter (i : Bool) {x : B} (hx : x ∈ hnnWordSpan φ v K) :
    v i*x ∈ hnnWordSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨w,a,hw,rfl⟩
    · simpa only [map_one,one_mul,HNNWord.eval] using
        hnnWordSpan_word φ v K (.single i a) 1 trivial
    · exact hnnWordSpan_left_word φ v K center r hc hr i a w hw
  | zero => simpa only [mul_zero] using (hnnWordSpan φ v K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (hnnWordSpan φ v K).add_mem ix iy
  | smul c x hx ix => simpa only [mul_smul_comm] using (hnnWordSpan φ v K).smul_mem c ix

theorem adjoin_le_hnnWordSpan :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range v)).toSubmodule ≤ hnnWordSpan φ v K := by
  intro x hx
  have hinv : ∀ z ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range v),
      ∀ y ∈ hnnWordSpan φ v K, z*y ∈ hnnWordSpan φ v K := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a,rfl⟩ | ⟨i,rfl⟩
      · exact fun y hy => hnnWordSpan_mul_base φ v K a hy
      · exact fun y hy => hnnWordSpan_mul_letter φ v K center r hc hr i hy
    | algebraMap c =>
      intro y hy
      simpa only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] using
        (hnnWordSpan φ v K).smul_mem c hy
    | add x y hx hy ix iy =>
      intro z hz
      simpa only [add_mul] using (hnnWordSpan φ v K).add_mem (ix z hz) (iy z hz)
    | mul x y hx hy ix iy =>
      intro z hz
      simpa only [mul_assoc] using ix (y*z) (iy z hz)
  have h1 : (1:B) ∈ hnnWordSpan φ v K := by
    simpa only [map_one] using hnnWordSpan_base φ v K 1
  simpa only [mul_one] using hinv x hx 1 h1

end HNNWords

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVector (f : A →ₚ[ℂ] ℂ) : f.GNS := (f.toPreGNS 1 : f.GNS)

@[simp] theorem gns_apply_coe (f : A →ₚ[ℂ] ℂ) (a b : A) :
    f.gnsStarAlgHom a (f.toPreGNS b : f.GNS) = (f.toPreGNS (a * b) : f.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom,
    ContinuousLinearMap.completion_apply_coe, PositiveLinearMap.leftMulMapPreGNS]

@[simp] theorem gns_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector]

theorem gnsVector_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f)) := by
  simp only [gns_apply_vector]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem gnsVector_coefficient (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ = f a := by
  simp [gnsVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] theorem gnsVector_norm_sq (f : A →ₚ[ℂ] ℂ) :
    ‖gnsVector f‖ ^ 2 = (f 1).re := by
  simp only [gnsVector, Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]
  exact Real.sq_sqrt (f.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

theorem positive_norm_apply_le (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  calc
    ‖f a‖ = ‖⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ‖ :=
      congrArg norm (gnsVector_coefficient f a).symm
    _ ≤ ‖gnsVector f‖ * ‖f.gnsStarAlgHom a (gnsVector f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖gnsVector f‖ * (‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖) := by
      gcongr
      exact (f.gnsStarAlgHom a).le_opNorm _
    _ ≤ ‖gnsVector f‖ * (‖a‖ * ‖gnsVector f‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a
    _ = (f 1).re * ‖a‖ := by rw [← gnsVector_norm_sq]; ring

def positiveCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_norm_apply_le f)

@[simp] theorem positiveCLM_apply (f : A →ₚ[ℂ] ℂ) (a : A) : positiveCLM f a = f a := rfl

theorem positiveCLM_norm (f : A →ₚ[ℂ] ℂ) : ‖positiveCLM f‖ = (f 1).re := by
  have hpos : 0 ≤ f 1 := f.map_nonneg zero_le_one
  apply le_antisymm
  · exact (positiveCLM f).opNorm_le_bound hpos.1 (positive_norm_apply_le f)
  · calc
      (f 1).re = ‖f 1‖ := Complex.re_eq_norm.mpr hpos
      _ = ‖positiveCLM f 1‖ := rfl
      _ ≤ ‖positiveCLM f‖ * ‖(1 : A)‖ := (positiveCLM f).le_opNorm 1
      _ ≤ ‖positiveCLM f‖ * 1 := by
        gcongr
        exact (IsStarProjection.one A).norm_le _
      _ = ‖positiveCLM f‖ := mul_one _

def positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ f.toLinearMap fun x hx => by
    have hx' := StarOrderedRing.nonneg_iff.mp hx
    refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => ?_) hx'
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨(hf a).2, (hf a).1.symm⟩
    · simpa only [map_add] using add_nonneg hx hy

@[simp] theorem positiveOfSquares_apply (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) (a : A) :
    positiveOfSquares f hf a = f a := rfl

@[simp] theorem positiveCLM_positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    positiveCLM (positiveOfSquares f hf) = f := by ext; rfl

theorem isState_iff (f : A →L[ℂ] ℂ) :
    IsState f ↔ f 1 = 1 ∧
      ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re := by
  constructor
  · rintro ⟨hnorm, hpos⟩
    refine ⟨?_, hpos⟩
    have hre : (f 1).re = 1 := by
      rw [← positiveOfSquares_apply f hpos 1, ← positiveCLM_norm,
        positiveCLM_positiveOfSquares, hnorm]
    have him : (f 1).im = 0 := by simpa using (hpos 1).1
    exact Complex.ext hre him
  · rintro ⟨hone, hpos⟩
    refine ⟨?_, hpos⟩
    have hn := positiveCLM_norm (positiveOfSquares f hpos)
    simpa only [positiveCLM_positiveOfSquares, positiveOfSquares_apply, hone,
      Complex.one_re] using hn

theorem gnsVector_norm_eq_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖gnsVector f‖ = 1 := by
  have hs := gnsVector_norm_sq f
  rw [hf, Complex.one_re] at hs
  nlinarith [norm_nonneg (gnsVector f)]

theorem gns_fix_of_value_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hfx : f x = 1) :
    f.gnsStarAlgHom x (gnsVector f) = gnsVector f := by
  have hn := gnsVector_norm_eq_one f hf
  have hy : ‖f.gnsStarAlgHom x (gnsVector f)‖ ≤ 1 := by
    calc
      _ ≤ ‖f.gnsStarAlgHom x‖ * ‖gnsVector f‖ := (f.gnsStarAlgHom x).le_opNorm _
      _ ≤ ‖x‖ * 1 := by
        gcongr
        · exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom x
        · exact hn.le
      _ ≤ 1 := by simpa using hx
  have hd := norm_sub_sq (𝕜 := ℂ) (gnsVector f) (f.gnsStarAlgHom x (gnsVector f))
  rw [gnsVector_coefficient, hfx, hn] at hd
  have hz : ‖gnsVector f - f.gnsStarAlgHom x (gnsVector f)‖ = 0 := by
    simp only [RCLike.re_to_complex, Complex.one_re, one_pow] at hd
    nlinarith [norm_nonneg (gnsVector f - f.gnsStarAlgHom x (gnsVector f)),
      norm_nonneg (f.gnsStarAlgHom x (gnsVector f))]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem positive_compression (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hself : IsSelfAdjoint x) (hfx : f x = 1) (a : A) :
    f (x * a * x) = f a := by
  have hfix := gns_fix_of_value_one f hf x hx hfx
  have hsa : ContinuousLinearMap.adjoint (f.gnsStarAlgHom x) = f.gnsStarAlgHom x := by
    change star (f.gnsStarAlgHom x) = f.gnsStarAlgHom x
    rw [← map_star, hself.star_eq]
  calc
    f (x * a * x) = ⟪gnsVector f,
        f.gnsStarAlgHom x (f.gnsStarAlgHom a (f.gnsStarAlgHom x (gnsVector f)))⟫_ℂ := by
      rw [← gnsVector_coefficient f (x * a * x)]
      simp only [map_mul, mul_apply_eq_comp]
    _ = ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ := by
      rw [hfix, ← ContinuousLinearMap.adjoint_inner_left, hsa, hfix]
    _ = f a := gnsVector_coefficient f a

theorem state_map_star (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) :
    f (star a) = star (f a) := map_star (positiveOfSquares f hf.2) a

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_norm_apply_le (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  simpa [hf.1] using f.le_opNorm a

theorem state_compression (f : A →L[ℂ] ℂ) (hf : IsState f)
    (x : A) (hx : ‖x‖ ≤ 1) (hself : IsSelfAdjoint x) (hfx : f x = 1) (a : A) :
    f (x * a * x) = f a :=
  positive_compression (positiveOfSquares f hf.2) ((isState_iff f).mp hf).1 x hx hself hfx a

def IsPureState (f : A →L[ℂ] ℂ) : Prop :=
  f ∈ Set.extremePoints ℝ {g : A →L[ℂ] ℂ | IsState g}

theorem convex_states : Convex ℝ {f : A →L[ℂ] ℂ | IsState f} := by
  intro f hf g hg a b ha hb hab
  apply (isState_iff _).mpr
  refine ⟨?_, ?_⟩
  · simp only [add_apply, smul_apply,
      ((isState_iff f).mp hf).1, ((isState_iff g).mp hg).1, ← add_smul, hab, one_smul]
  · intro x
    simp only [add_apply, smul_apply,
      Complex.add_im, Complex.add_re, Complex.smul_im, Complex.smul_re]
    exact ⟨by rw [(hf.2 x).1, (hg.2 x).1]; simp,
      add_nonneg (mul_nonneg ha (hf.2 x).2) (mul_nonneg hb (hg.2 x).2)⟩

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_projection_face (f g : A →L[ℂ] ℂ) (hf : IsState f) (hg : IsState g)
    (p : A) (hp : IsStarProjection p) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (heq : (a • f + b • g) p = 1) : f p = 1 ∧ g p = 1 := by
  have hfim : (f p).im = 0 := by
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using (hf.2 p).1
  have hgim : (g p).im = 0 := by
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using (hg.2 p).1
  have hfr : (f p).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le f hf p).trans (hp.norm_le _))
  have hgr : (g p).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le g hg p).trans (hp.norm_le _))
  have heqr := congrArg Complex.re heq
  simp only [add_apply, smul_apply,
    Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul] at heqr
  have hfr' : (f p).re = 1 := by nlinarith
  have hgr' : (g p).re = 1 := by nlinarith
  exact ⟨Complex.ext hfr' hfim, Complex.ext hgr' hgim⟩

def Peaks (p : ℕ → A) (f : A →L[ℂ] ℂ) : Prop :=
  (∀ n, IsStarProjection (p n)) ∧ Antitone p ∧ IsState f ∧
    (∀ n, f (p n) = 1) ∧
    ∀ g : A →L[ℂ] ℂ, IsState g → (∀ n, g (p n) = 1) → g = f

omit [StarOrderedRing A] in

theorem Peaks.isPureState {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hp.2.2.1, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hfaces : ∀ n, g (p n) = 1 ∧ h (p n) = 1 := by
    intro n
    apply state_projection_face g h hg hh (p n) (hp.1 n) a b ha hb hab
    rw [heq]
    exact hp.2.2.2.1 n
  exact ⟨hp.2.2.2.2 g hg (fun n => (hfaces n).1),
    hp.2.2.2.2 h hh (fun n => (hfaces n).2)⟩

theorem state_nonneg (f : A →L[ℂ] ℂ) (hf : IsState f) {x : A} (hx : 0 ≤ x) :
    0 ≤ f x := (positiveOfSquares f hf.2).map_nonneg hx

theorem state_contraction_face (f g : A →L[ℂ] ℂ) (hf : IsState f) (hg : IsState g)
    (x : A) (hx : 0 ≤ x) (hn : ‖x‖ ≤ 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (heq : (a • f + b • g) x = 1) : f x = 1 ∧ g x = 1 := by
  have hfim : (f x).im = 0 := (state_nonneg f hf hx).2.symm
  have hgim : (g x).im = 0 := (state_nonneg g hg hx).2.symm
  have hfr : (f x).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le f hf x).trans hn)
  have hgr : (g x).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le g hg x).trans hn)
  have heqr := congrArg Complex.re heq
  simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re,
    Complex.one_re, smul_eq_mul] at heqr
  have hfr' : (f x).re = 1 := by nlinarith
  have hgr' : (g x).re = 1 := by nlinarith
  exact ⟨Complex.ext hfr' hfim, Complex.ext hgr' hgim⟩

theorem state_excision_error (f g : A →L[ℂ] ℂ) (hg : IsState g) (a x : A)
    (hx : 0 ≤ x) (hn : ‖x‖ ≤ 1) (hgx : g x = 1) :
    ‖g a - f a‖ ≤ ‖x * (a - f a • (1 : A)) * x‖ := by
  have hcomp := state_compression g hg x hn (IsSelfAdjoint.of_nonneg hx) hgx
  calc
    ‖g a - f a‖ = ‖g (a - f a • (1 : A))‖ := by
      rw [map_sub, map_smul, ((isState_iff g).mp hg).1, smul_eq_mul, mul_one]
    _ = ‖g (x * (a - f a • (1 : A)) * x)‖ := congrArg norm (hcomp _).symm
    _ ≤ ‖x * (a - f a • (1 : A)) * x‖ := state_norm_apply_le g hg _

theorem pure_of_dense_excision (f : A →L[ℂ] ℂ) (hf : IsState f)
    (D : Set A) (hD : Dense D)
    (hexc : ∀ a ∈ D, ∀ ε : ℝ, 0 < ε → ∃ x : A,
      0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x * (a - f a • (1 : A)) * x‖ < ε) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hvals : ∀ z ∈ D, g z = f z ∧ h z = f z := by
    intro z hz
    have hsmall (ε : ℝ) (hε : 0 < ε) : ‖g z - f z‖ < ε ∧ ‖h z - f z‖ < ε := by
      obtain ⟨x, hx, hn, hfx, herr⟩ := hexc z hz ε hε
      have hface := state_contraction_face g h hg hh x hx hn a b ha hb hab
        (by rw [heq]; exact hfx)
      exact ⟨(state_excision_error f g hg z x hx hn hface.1).trans_lt herr,
        (state_excision_error f h hh z x hx hn hface.2).trans_lt herr⟩
    have hg0 : ‖g z - f z‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      simpa only [zero_add] using (hsmall ε hε).1.le
    have hh0 : ‖h z - f z‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      simpa only [zero_add] using (hsmall ε hε).2.le
    exact ⟨eq_of_norm_sub_eq_zero (le_antisymm hg0 (norm_nonneg _)),
      eq_of_norm_sub_eq_zero (le_antisymm hh0 (norm_nonneg _))⟩
  exact ⟨ContinuousLinearMap.ext (congrFun (g.continuous.ext_on hD f.continuous
      (fun z hz => (hvals z hz).1))),
    ContinuousLinearMap.ext (congrFun (h.continuous.ext_on hD f.continuous
      (fun z hz => (hvals z hz).2)))⟩

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def starAlgHomCLM (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem starAlgHomCLM_apply (φ : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomCLM φ a = φ a := rfl

def restrictState (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.comp (starAlgHomCLM φ)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem restrictState_apply (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (a : A) :
    restrictState φ f a = f (φ a) := rfl

theorem isState_restrict (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (hf : IsState f) :
    IsState (restrictState φ f) := by
  apply (isState_iff _).mpr
  refine ⟨?_, ?_⟩
  · simp only [restrictState_apply, map_one, ((isState_iff f).mp hf).1]
  · intro a
    simpa only [restrictState_apply, map_mul, map_star] using hf.2 (φ a)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in

theorem restrictState_convex (φ : A →⋆ₐ[ℂ] B) (f g : B →L[ℂ] ℂ) (a b : ℝ) :
    restrictState φ (a • f + b • g) = a • restrictState φ f + b • restrictState φ g := by
  ext x
  rfl

theorem unique_lift_pure (φ : A →⋆ₐ[ℂ] B) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : B →L[ℂ] ℂ) (hF : IsState F) (hres : restrictState φ F = f)
    (hunique : ∀ G : B →L[ℂ] ℂ, IsState G → restrictState φ G = f → G = F) :
    IsPureState F := by
  rw [IsPureState, mem_extremePoints] at hf ⊢
  refine ⟨hF, ?_⟩
  intro G hG H hH hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hseg' : f ∈ openSegment ℝ (restrictState φ G) (restrictState φ H) := by
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [← restrictState_convex, heq, hres]
  obtain ⟨hGres, hHres⟩ := hf.2 _ (isState_restrict φ G hG) _
    (isState_restrict φ H hH) hseg'
  exact ⟨hunique G hG hGres, hunique H hH hHres⟩

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_map_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) :
    π 1 = 1 := by
  have hp : IsIdempotentElem (π 1) := by
    change π 1 * π 1 = π 1
    rw [← map_mul, one_mul]
  have hr (a : A) (x : H) : π a x ∈ (π 1).range := by
    refine ⟨π a x, ?_⟩
    change (π 1 * π a) x = π a x
    rw [← map_mul, one_mul]
  rcases hπ.2 (π 1).range (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp) (fun a x _ => hr a x) with hz | ht
  · exfalso
    apply hπ.1
    ext a x
    have h := hr a x
    rw [hz] at h
    exact h
  · ext x
    have hx : x ∈ (π 1).range := by rw [ht]; trivial
    obtain ⟨y, rfl⟩ := hx
    change (π 1 * π 1) y = π 1 y
    rw [hp]

def orbitMap (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →ₗ[ℂ] H where
  toFun a := π a x
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem orbitMap_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    orbitMap π x a = π a x := rfl

theorem irreducible_vector_cyclic (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (x : H) (hx : x ≠ 0) : DenseRange (fun a : A => π a x) := by
  let M := (orbitMap π x).range
  have hm (a : A) : M.map (π a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [orbitMap, map_mul, mul_apply_eq_comp]
  have hinv (a : A) (y : H) (hy : y ∈ M.topologicalClosure) :
      π a y ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hm a)
    apply Submodule.topologicalClosure_map (π a) M
    exact ⟨y, hy, rfl⟩
  have hxM : x ∈ M := by
    refine ⟨1, ?_⟩
    simp [orbitMap, irreducible_map_one π hπ]
  have hxcl : x ∈ M.topologicalClosure := M.le_topologicalClosure hxM
  have htop : M.topologicalClosure = ⊤ := by
    rcases hπ.2 M.topologicalClosure M.isClosed_topologicalClosure hinv with h | h
    · exact (hx (by simpa [h] using hxcl)).elim
    · exact h
  exact (Submodule.dense_iff_topologicalClosure_eq_top.mpr htop : Dense (M : Set H))

def orbitCLM (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] H :=
  (orbitMap π x).mkContinuous ‖x‖ fun a => by
    calc
      ‖π a x‖ ≤ ‖π a‖ * ‖x‖ := (π a).le_opNorm x
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg x)
      _ = ‖x‖ * ‖a‖ := mul_comm _ _

def vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (orbitCLM π x)

@[simp] theorem vectorFunctional_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x a = ⟪x, π a x⟫_ℂ := rfl

@[simp] theorem vectorFunctional_square (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x (star a * a) = (‖π a x‖ : ℂ) ^ 2 := by
  rw [vectorFunctional_apply, map_mul, map_star]
  change ⟪x, (ContinuousLinearMap.adjoint (π a)) ((π a) x)⟫_ℂ = _
  simp [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]

@[simp] theorem vectorFunctional_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (x : H) :
    vectorFunctional π x 1 = (‖x‖ : ℂ) ^ 2 := by
  simp [hone, inner_self_eq_norm_sq_to_K]

theorem vectorFunctional_norm_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    ‖vectorFunctional π x‖ ≤ ‖x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro a
  calc
    ‖vectorFunctional π x a‖ = ‖⟪x, π a x⟫_ℂ‖ := rfl
    _ ≤ ‖x‖ * ‖π a x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖π a‖ * ‖x‖) := by gcongr; exact (π a).le_opNorm x
    _ ≤ ‖x‖ * (‖a‖ * ‖x‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = ‖x‖ ^ 2 * ‖a‖ := by ring

theorem isState_vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : ‖x‖ = 1) : IsState (vectorFunctional π x) := by
  constructor
  · apply le_antisymm
    · simpa [hx] using vectorFunctional_norm_le π x
    · calc
        1 = ‖vectorFunctional π x 1‖ := by simp [vectorFunctional_one π hone, hx]
        _ ≤ ‖vectorFunctional π x‖ * ‖(1 : A)‖ := (vectorFunctional π x).le_opNorm 1
        _ ≤ ‖vectorFunctional π x‖ * 1 := by
          gcongr
          exact (IsStarProjection.one A).norm_le _
        _ = ‖vectorFunctional π x‖ := mul_one _
  · intro a
    rw [vectorFunctional_square]
    simp only [← Complex.ofReal_pow, Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact sq_nonneg _

theorem irreducible_vector_state (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : H) (hx : ‖x‖ = 1) : IsState (vectorFunctional π x) :=
  isState_vectorFunctional π (irreducible_map_one π hπ) x hx

theorem invariant_orthogonal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H)
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) :
    ∀ a : A, ∀ x ∈ Mᗮ, π a x ∈ Mᗮ := by
  intro a x hx y hy
  have hz := hx (π (star a) y) (hM (star a) y hy)
  rw [map_star] at hz
  exact (ContinuousLinearMap.adjoint_inner_left (π a) x y).symm.trans hz

theorem invariant_starProjection_commute (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) (a : A) (x : H) :
    M.starProjection (π a x) = π a (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hM a _ (M.starProjection_apply_mem x)
  · rw [← map_sub]
    exact invariant_orthogonal π M hM a _ (M.sub_starProjection_mem_orthogonal x)

theorem vectorFunctional_add_reducing (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (x y : H) (hx : x ∈ M) (hy : y ∈ Mᗮ) :
    vectorFunctional π (x + y) = vectorFunctional π x + vectorFunctional π y := by
  ext a
  simp only [vectorFunctional_apply, map_add, inner_add_left, inner_add_right, add_apply]
  have hxy : ⟪x, π a y⟫_ℂ = 0 := invariant_orthogonal π M hM a y hy x hx
  have hyx : ⟪y, π a x⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    simp only [hy _ (hM a x hx), map_zero]
  rw [hxy, hyx]
  simp only [add_zero, zero_add]

variable [PartialOrder A] [StarOrderedRing A]

theorem normalized_vector_isState (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : x ≠ 0) :
    IsState ((‖x‖ ^ 2)⁻¹ • vectorFunctional π x) := by
  apply (isState_iff _).mpr
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  constructor
  · rw [smul_apply, vectorFunctional_one π hone, ← Complex.ofReal_pow]
    change (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 hn), Complex.ofReal_one]
  · intro a
    rw [smul_apply, vectorFunctional_square]
    simp only [Complex.smul_im, Complex.smul_re, ← Complex.ofReal_pow,
      Complex.ofReal_im, Complex.ofReal_re, smul_eq_mul, mul_zero, true_and]
    positivity

omit [PartialOrder A] [StarOrderedRing A] in

theorem cyclic_closed_invariant_top (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a : A => π a ξ)) (M : Submodule ℂ H)
    (hclosed : IsClosed (M : Set H)) (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (hξ : ξ ∈ M) : M = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  apply closure_minimal (s := Set.range (fun a : A => π a ξ)) _ hclosed (hcyc x)
  rintro y ⟨a, rfl⟩
  exact hinv a ξ hξ

theorem pure_cyclic_irreducible (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (hcyc : DenseRange (fun a : A => π a ξ))
    (hpure : IsPureState (vectorFunctional π ξ)) : IsIrreducible π := by
  refine ⟨?_, ?_⟩
  · intro hz
    have h : ξ = 0 := by
      calc
        ξ = π 1 ξ := by rw [hone]; rfl
        _ = 0 := by rw [hz]; rfl
    simp [h] at hξ
  · intro M hclosed hinv
    let : IsClosed (M : Set H) := hclosed
    let u := M.starProjection ξ
    let v := ξ - u
    have huM : u ∈ M := M.starProjection_apply_mem ξ
    have hvM : v ∈ Mᗮ := M.sub_starProjection_mem_orthogonal ξ
    by_cases hu : u = 0
    · left
      apply M.orthogonal_eq_top_iff.mp
      apply cyclic_closed_invariant_top π ξ hcyc Mᗮ M.isClosed_orthogonal
        (invariant_orthogonal π M hinv)
      simpa only [v, hu, sub_zero] using hvM
    by_cases hv : v = 0
    · right
      apply cyclic_closed_invariant_top π ξ hcyc M hclosed hinv
      have h : ξ = u := sub_eq_zero.mp hv
      rwa [h]
    have ha : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hb : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hab : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := by
      have h := Submodule.norm_sq_eq_add_norm_sq_starProjection ξ M
      rw [hξ, one_pow, Submodule.starProjection_orthogonal_val] at h
      exact h.symm
    have huv : u + v = ξ := by dsimp [v]; abel
    have hseg : vectorFunctional π ξ ∈ openSegment ℝ
        ((‖u‖ ^ 2)⁻¹ • vectorFunctional π u)
        ((‖v‖ ^ 2)⁻¹ • vectorFunctional π v) := by
      refine ⟨‖u‖ ^ 2, ‖v‖ ^ 2, ha, hb, hab, ?_⟩
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt ha),
        mul_inv_cancel₀ (ne_of_gt hb), one_smul, one_smul]
      rw [← vectorFunctional_add_reducing π M hinv u v huM hvM, huv]
    have huf : (‖u‖ ^ 2)⁻¹ • vectorFunctional π u = vectorFunctional π ξ :=
      (((mem_extremePoints.mp hpure).2 _ (normalized_vector_isState π hone u hu)
        _ (normalized_vector_isState π hone v hv) hseg).1)
    have hgu : vectorFunctional π u = ‖u‖ ^ 2 • vectorFunctional π ξ := by
      rw [← huf, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    have hPu : M.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr huM
    have coeff (a : A) : ⟪u, π a ξ⟫_ℂ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := by
      calc
        ⟪u, π a ξ⟫_ℂ = ⟪u, M.starProjection (π a ξ)⟫_ℂ := by
          rw [← M.inner_starProjection_left_eq_right, hPu]
        _ = vectorFunctional π u a := by
          rw [invariant_starProjection_commute π M hinv]
          rfl
        _ = (‖u‖ ^ 2) • ⟪ξ, π a ξ⟫_ℂ := by rw [hgu]; rfl
        _ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := (inner_smul_left_eq_smul _ _ _).symm
    have hscalar : u = (‖u‖ ^ 2) • ξ := by
      apply ext_inner_right ℂ
      have h := hcyc.equalizer
        (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
        (funext coeff)
      exact congrFun h
    have hscale : (‖u‖ ^ 2 : ℝ) • u = u := by
      calc
        (‖u‖ ^ 2 : ℝ) • u = M.starProjection ((‖u‖ ^ 2 : ℝ) • ξ) := by
          exact ((M.starProjection.restrictScalars ℝ).map_smul (‖u‖ ^ 2) ξ).symm
        _ = M.starProjection u := by rw [← hscalar]
        _ = u := hPu
    have hnorm := congrArg norm hscale
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
    have hn := norm_pos_iff.mpr hu
    exfalso
    have h1 : ‖u‖ ^ 2 = 1 := by nlinarith
    linarith

theorem pure_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f) (hfp : IsPureState f) :
    IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom := by
  let g := positiveOfSquares f hf.2
  have hone : g 1 = 1 := ((isState_iff f).mp hf).1
  have hcoeff : vectorFunctional g.gnsNonUnitalStarAlgHom (gnsVector g) = f := by
    ext a
    exact gnsVector_coefficient g a
  apply pure_cyclic_irreducible g.gnsNonUnitalStarAlgHom
    (show g.gnsStarAlgHom 1 = 1 from map_one _) (gnsVector g)
    (gnsVector_norm_eq_one g hone) (gnsVector_cyclic g)
  rwa [hcoeff]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_denseRange (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hcomm : ∀ a : A, Commute T (π a)) : DenseRange T := by
  let M := T.range
  have hinv (a : A) : M.map (π a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨π a x, ?_⟩
    exact congrArg (fun S : H →L[ℂ] H => S x) (hcomm a).eq
  have hcl (a : A) (x : H) (hx : x ∈ M.topologicalClosure) :
      π a x ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hinv a)
    apply Submodule.topologicalClosure_map (π a) M
    exact ⟨x, hx, rfl⟩
  rcases hπ.2 M.topologicalClosure M.isClosed_topologicalClosure hcl with hz | ht
  · exfalso
    apply hT
    ext x
    have hx : T x ∈ M.topologicalClosure := M.le_topologicalClosure ⟨x, rfl⟩
    rw [hz] at hx
    exact hx
  · intro x
    have hx : x ∈ M.topologicalClosure := by rw [ht]; trivial
    exact hx

theorem commutant_mul_eq_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (S T : H →L[ℂ] H)
    (hcomm : ∀ a : A, Commute T (π a)) (hz : S * T = 0) : S = 0 ∨ T = 0 := by
  by_cases hT : T = 0
  · exact Or.inr hT
  · left
    apply DFunLike.coe_injective
    change (fun x => S x) = (fun _ => 0)
    apply (irreducible_commutant_denseRange π hπ T hT hcomm).equalizer
      S.continuous continuous_const
    funext x
    exact congrArg (fun R : H →L[ℂ] H => R x) hz

theorem irreducible_commutant_selfAdjoint_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ r : ℝ, T = r • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, Subsingleton.elim _ _⟩
  let : Nontrivial H := hH
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) T hT
  refine ⟨r, ?_⟩
  have unique (x y : ℝ) (hx : x ∈ spectrum ℝ T) (hy : y ∈ spectrum ℝ T) : ¬ x < y := by
    intro hxy
    let c := (x + y) / 2
    let f : ℝ → ℝ := fun t => max (t - c) 0
    let g : ℝ → ℝ := fun t => max (c - t) 0
    have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
    have hg : Continuous g := (continuous_const.sub continuous_id).max continuous_const
    have hfg (t : ℝ) : f t * g t = 0 := by
      dsimp [f, g]
      by_cases h : t ≤ c
      · rw [max_eq_right (sub_nonpos.mpr h), zero_mul]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), mul_zero]
    have hzero : cfc f T * cfc g T = 0 := by
      rw [← cfc_mul f g T hf.continuousOn hg.continuousOn]
      rw [cfc_congr (g := fun _ : ℝ => 0) (fun t _ => hfg t), cfc_const_zero]
    rcases commutant_mul_eq_zero π hπ (cfc f T) (cfc g T)
      (fun a => hT.commute_cfc (hcomm a) g) hzero with hz | hz
    · have heq : cfc f T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hT hy
      dsimp [f, c] at hval
      have hpos : 0 < y - (x + y) / 2 := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
    · have heq : cfc g T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hg.continuousOn continuousOn_const hT hx
      dsimp [g, c] at hval
      have hpos : 0 < (x + y) / 2 - x := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
  have hspec : spectrum ℝ T ⊆ {r} := by
    intro t ht
    exact le_antisymm (not_lt.mp (unique r t hr ht)) (not_lt.mp (unique t r ht hr))
  simpa [Algebra.algebraMap_eq_smul_one] using
    CFC.eq_algebraMap_of_spectrum_subset_singleton T r hspec hT

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def dominatedPreGNS (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    f.PreGNS →L[ℂ] g.PreGNS :=
  (g.toPreGNS.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous (Real.sqrt C) fun x => by
    change √(g (star (f.ofPreGNS x) * f.ofPreGNS x)).re ≤
      √C * √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt (hdom _)

@[simp] theorem dominatedPreGNS_apply (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    dominatedPreGNS f g C hC hdom (f.toPreGNS a) = g.toPreGNS a := rfl

def dominatedGNS (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    f.GNS →L[ℂ] g.GNS := (dominatedPreGNS f g C hC hdom).completion

@[simp] theorem dominatedGNS_apply_coe (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    dominatedGNS f g C hC hdom (f.toPreGNS a : f.GNS) = (g.toPreGNS a : g.GNS) := by
  simp [dominatedGNS]

@[simp] theorem dominatedGNS_apply_vector (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    dominatedGNS f g C hC hdom (gnsVector f) = gnsVector g := by
  simp [gnsVector]

theorem dominatedGNS_intertwines (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    (dominatedGNS f g C hC hdom).comp (f.gnsStarAlgHom a) =
      (g.gnsStarAlgHom a).comp (dominatedGNS f g C hC hdom) := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
  funext b
  change dominatedGNS f g C hC hdom (f.gnsStarAlgHom a (f.gnsStarAlgHom b (gnsVector f))) =
    g.gnsStarAlgHom a (dominatedGNS f g C hC hdom (f.gnsStarAlgHom b (gnsVector f)))
  simp only [gns_apply_vector, gns_apply_coe, dominatedGNS_apply_coe]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem intertwiner_adjoint_comp_commute
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (T : H →L[ℂ] K)
    (hT : ∀ a : A, T.comp (π a) = (ρ a).comp T) (a : A) :
    Commute (T.adjoint.comp T) (π a) := by
  have hstar := congrArg ContinuousLinearMap.adjoint (hT (star a))
  simp only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] at hstar
  change (T.adjoint.comp T).comp (π a) = (π a).comp (T.adjoint.comp T)
  rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc, ← hstar,
    ContinuousLinearMap.comp_assoc]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positive_eq_smul_of_gns_irreducible (f g : A →ₚ[ℂ] ℂ)
    (hπ : IsIrreducible f.gnsNonUnitalStarAlgHom) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    ∃ r : ℝ, ∀ a : A, g a = r • f a := by
  let T := dominatedGNS f g C hC hdom
  have hInt (a : A) : T.comp (f.gnsStarAlgHom a) = (g.gnsStarAlgHom a).comp T :=
    dominatedGNS_intertwines f g C hC hdom a
  have hcomm (a : A) : Commute (T.adjoint.comp T) (f.gnsStarAlgHom a) :=
    intertwiner_adjoint_comp_commute f.gnsNonUnitalStarAlgHom g.gnsNonUnitalStarAlgHom T hInt a
  have hself : IsSelfAdjoint (T.adjoint.comp T) := by
    change (T.adjoint.comp T).adjoint = T.adjoint.comp T
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨r, hr⟩ := irreducible_commutant_selfAdjoint_scalar
    f.gnsNonUnitalStarAlgHom hπ (T.adjoint.comp T) hself hcomm
  refine ⟨r, ?_⟩
  intro a
  have hξ : T (gnsVector f) = gnsVector g := dominatedGNS_apply_vector f g C hC hdom
  have hact : T (f.gnsStarAlgHom a (gnsVector f)) = g.gnsStarAlgHom a (gnsVector g) := by
    simpa only [ContinuousLinearMap.comp_apply, hξ] using
      congrArg (fun R => R (gnsVector f)) (hInt a)
  calc
    g a = ⟪gnsVector g, g.gnsStarAlgHom a (gnsVector g)⟫_ℂ := (gnsVector_coefficient g a).symm
    _ = ⟪T (gnsVector f), T (f.gnsStarAlgHom a (gnsVector f))⟫_ℂ := by rw [hξ, hact]
    _ = ⟪gnsVector f, (T.adjoint.comp T) (f.gnsStarAlgHom a (gnsVector f))⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right T _ _).symm
    _ = r • f a := by
      rw [hr]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right_eq_smul, gnsVector_coefficient]

theorem isPureState_of_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f)
    (hπ : IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have dominated (g h : A →L[ℂ] ℂ) (hg : IsState g) (hh : IsState h)
      (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (heq : a • g + b • h = f) : g = f := by
    have hdom (x : A) : (g (star x * x)).re ≤ a⁻¹ * (f (star x * x)).re := by
      have hval := congrArg (fun k : A →L[ℂ] ℂ => (k (star x * x)).re) heq
      simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul] at hval
      have hgpos := (hg.2 x).2
      have hhpos := (hh.2 x).2
      rw [mul_comm a⁻¹, ← div_eq_mul_inv, le_div_iff₀ ha]
      nlinarith
    obtain ⟨r, hr⟩ := positive_eq_smul_of_gns_irreducible
      (positiveOfSquares f hf.2) (positiveOfSquares g hg.2) hπ a⁻¹ (le_of_lt (inv_pos.mpr ha)) hdom
    have hone := hr 1
    simp only [positiveOfSquares_apply, ((isState_iff f).mp hf).1,
      ((isState_iff g).mp hg).1] at hone
    have hrone : r = 1 := by
      have hre := congrArg Complex.re hone
      simpa only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] using hre.symm
    ext x
    simpa only [hrone, one_smul, positiveOfSquares_apply] using hr x
  exact ⟨dominated g h hg hh a b ha hb heq,
    dominated h g hh hg b a hb ha (by rwa [add_comm])⟩

theorem isPureState_iff_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsPureState f ↔ IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom :=
  ⟨pure_gns_irreducible f hf, isPureState_of_gns_irreducible f hf⟩

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cyclicPreGNS (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.PreGNS →ₗᵢ[ℂ] H where
  toLinearMap := (orbitMap π ξ).comp f.ofPreGNS.toLinearMap
  norm_map' x := by
    change ‖π (f.ofPreGNS x) ξ‖ = √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [hcoeff, map_mul, map_star]
    change ‖π (f.ofPreGNS x) ξ‖ =
      √(⟪ξ, (π (f.ofPreGNS x)).adjoint (π (f.ofPreGNS x) ξ)⟫_ℂ).re
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    change ‖π (f.ofPreGNS x) ξ‖ = √(‖π (f.ofPreGNS x) ξ‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm

@[simp] theorem cyclicPreGNS_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicPreGNS f π ξ hcoeff (f.toPreGNS a) = π a ξ := rfl

def cyclicGNSMap (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.GNS →L[ℂ] H :=
  (cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion

@[simp] theorem cyclicGNSMap_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicGNSMap f π ξ hcoeff (f.toPreGNS a : f.GNS) = π a ξ := by
  simp [cyclicGNSMap]

theorem cyclicGNSMap_norm (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (x : f.GNS) :
    ‖cyclicGNSMap f π ξ hcoeff x‖ = ‖x‖ := by
  have heq : (fun y : f.GNS => ‖cyclicGNSMap f π ξ hcoeff y‖) = fun y => ‖y‖ := by
    apply Completion.denseRange_coe.equalizer (by fun_prop) (by fun_prop)
    funext y
    change ‖(cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion (y : f.GNS)‖ = ‖(y : f.GNS)‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe]
    exact (cyclicPreGNS f π ξ hcoeff).norm_map y
  exact congrFun heq x

def cyclicGNSIsometry (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.GNS →ₗᵢ[ℂ] H where
  toLinearMap := (cyclicGNSMap f π ξ hcoeff).toLinearMap
  norm_map' := cyclicGNSMap_norm f π ξ hcoeff

theorem cyclicGNSIsometry_surjective (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) :
    Function.Surjective (cyclicGNSIsometry f π ξ hcoeff) := by
  have hrange : IsClosed (Set.range (cyclicGNSIsometry f π ξ hcoeff)) :=
    (cyclicGNSIsometry f π ξ hcoeff).isometry.isClosedEmbedding.isClosed_range
  have htop : Set.range (cyclicGNSIsometry f π ξ hcoeff) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hcyclic.closure_range]
    apply closure_minimal _ hrange
    rintro _ ⟨a, rfl⟩
    exact ⟨(f.toPreGNS a : f.GNS), cyclicGNSMap_apply f π ξ hcoeff a⟩
  exact Set.range_eq_univ.mp htop

def cyclicGNSEquiv (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) : f.GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (cyclicGNSIsometry f π ξ hcoeff)
    (cyclicGNSIsometry_surjective f π ξ hcoeff hcyclic)

theorem cyclicGNSEquiv_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) (a : A) (x : f.GNS) :
    cyclicGNSEquiv f π ξ hcoeff hcyclic (f.gnsNonUnitalStarAlgHom a x) =
      π a (cyclicGNSEquiv f π ξ hcoeff hcyclic x) := by
  change cyclicGNSMap f π ξ hcoeff (f.gnsStarAlgHom a x) =
    π a (cyclicGNSMap f π ξ hcoeff x)
  have heq : (fun y : f.GNS => cyclicGNSMap f π ξ hcoeff (f.gnsStarAlgHom a y)) =
      fun y => π a (cyclicGNSMap f π ξ hcoeff y) := by
    apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
    funext b
    simp only [Function.comp_apply, gns_apply_vector, gns_apply_coe, cyclicGNSMap_apply,
      map_mul, mul_apply_eq_comp]
  exact congrFun heq x

end GNS

section FaithfulMoments

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem faithful_gns_injective (f : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0) :
    Function.Injective f.gnsStarAlgHom := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← gnsVector_coefficient, map_mul, map_star, map_sub, hab, sub_self]
  simp

def gnsOrbit (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] f.GNS :=
  LinearMap.mkContinuous
    { toFun := fun a => f.gnsStarAlgHom a (gnsVector f)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    ‖gnsVector f‖ fun a => by
      calc
        ‖f.gnsStarAlgHom a (gnsVector f)‖ ≤ ‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖ :=
          (f.gnsStarAlgHom a).le_opNorm _
        _ ≤ ‖a‖ * ‖gnsVector f‖ := by
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ _
        _ = ‖gnsVector f‖ * ‖a‖ := mul_comm _ _

@[simp] theorem gnsOrbit_apply (f : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbit f a = (f.toPreGNS a : f.GNS) := gns_apply_vector f a

theorem gnsOrbit_dense (f : A →ₚ[ℂ] ℂ) : DenseRange (gnsOrbit f) :=
  gnsVector_cyclic f

@[simp] theorem gnsOrbit_norm (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsOrbit f a‖ = Real.sqrt (f (star a * a)).re := by
  simp only [gnsOrbit_apply, Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ)
    (htr : ∀ r : R, f (i r) = g (j r))

def momentGNSEquiv : f.GNS ≃ₗᵢ[ℂ] g.GNS :=
  (LinearEquiv.refl ℂ R).extendOfIsometry
    ((gnsOrbit f).toLinearMap.comp i.toAlgHom.toLinearMap)
    ((gnsOrbit g).toLinearMap.comp j.toAlgHom.toLinearMap)
    ((gnsOrbit_dense f).comp hi (gnsOrbit f).continuous)
    ((gnsOrbit_dense g).comp hj (gnsOrbit g).continuous)
    (fun r => by
      change ‖gnsOrbit g (j r)‖ = ‖gnsOrbit f (i r)‖
      simp only [gnsOrbit_norm, ← map_mul, ← map_star, htr])

@[simp] theorem momentGNSEquiv_apply (r : R) :
    momentGNSEquiv i j hi hj f g htr (gnsOrbit f (i r)) = gnsOrbit g (j r) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r

theorem momentGNSEquiv_intertwines (r : R) (x : f.GNS) :
    momentGNSEquiv i j hi hj f g htr (f.gnsStarAlgHom (i r) x) =
      g.gnsStarAlgHom (j r) (momentGNSEquiv i j hi hj f g htr x) := by
  let U := momentGNSEquiv i j hi hj f g htr
  have heq : (fun y : f.GNS => U (f.gnsStarAlgHom (i r) y)) =
      fun y => g.gnsStarAlgHom (j r) (U y) := by
    apply ((gnsOrbit_dense f).comp hi (gnsOrbit f).continuous).equalizer
      (by fun_prop) (by fun_prop)
    funext s
    change U (f.gnsStarAlgHom (i r) (gnsOrbit f (i s))) =
      g.gnsStarAlgHom (j r) (U (gnsOrbit f (i s)))
    have hmul (a b : A) : f.gnsStarAlgHom a (gnsOrbit f b) = gnsOrbit f (a * b) := by
      simp only [gnsOrbit_apply, gns_apply_coe]
    have hmul' (a b : B) : g.gnsStarAlgHom a (gnsOrbit g b) = gnsOrbit g (a * b) := by
      simp only [gnsOrbit_apply, gns_apply_coe]
    rw [hmul, ← map_mul]
    change momentGNSEquiv i j hi hj f g htr (gnsOrbit f (i (r * s))) = _
    rw [momentGNSEquiv_apply, momentGNSEquiv_apply, hmul', map_mul]
  exact congrFun heq x

include hi hj htr in

theorem norm_eq_of_faithful_moments
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (r : R) : ‖j r‖ = ‖i r‖ := by
  let U := momentGNSEquiv i j hi hj f g htr
  have heq : U.conjStarAlgEquiv (f.gnsStarAlgHom (i r)) = g.gnsStarAlgHom (j r) := by
    ext x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    change momentGNSEquiv i j hi hj f g htr (f.gnsStarAlgHom (i r) (U.symm x)) = _
    rw [momentGNSEquiv_intertwines]
    simp [U]
  calc
    ‖j r‖ = ‖g.gnsStarAlgHom (j r)‖ :=
      (NonUnitalStarAlgHom.norm_map _ (faithful_gns_injective g hg) _).symm
    _ = ‖U.conjStarAlgEquiv (f.gnsStarAlgHom (i r))‖ := congrArg norm heq.symm
    _ = ‖f.gnsStarAlgHom (i r)‖ :=
      NonUnitalStarAlgHom.norm_map
        (U.conjStarAlgEquiv.toStarAlgHom :
          (f.GNS →L[ℂ] f.GNS) →⋆ₐ[ℂ] (g.GNS →L[ℂ] g.GNS))
        U.conjStarAlgEquiv.injective _
    _ = ‖i r‖ := NonUnitalStarAlgHom.norm_map _ (faithful_gns_injective f hf) _

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

def starAlgEquivOfDenseNorm (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j) (hnorm : ∀ r, ‖j r‖ = ‖i r‖) : A ≃⋆ₐ[ℂ] B := by
  let U : A ≃ₗᵢ[ℂ] B := (LinearEquiv.refl ℂ R).extendOfIsometry
    i.toAlgHom.toLinearMap j.toAlgHom.toLinearMap hi hj hnorm
  have hU (r : R) : U (i r) = j r :=
    LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r
  have hleft (r : R) (b : A) : U (i r * b) = j r * U b := by
    have h := hi.equalizer (g := fun x : A => U (i r * x))
      (h := fun x : A => j r * U x) (by fun_prop) (by fun_prop) (by
        funext s
        simp only [Function.comp_apply, ← map_mul, hU])
    exact congrFun h b
  have hmul (a b : A) : U (a * b) = U a * U b := by
    have h := hi.equalizer (g := fun x : A => U (x * b))
      (h := fun x : A => U x * U b) (by fun_prop) (by fun_prop) (by
        funext r
        simp only [Function.comp_apply, hU, hleft])
    exact congrFun h a
  have hstar (a : A) : U (star a) = star (U a) := by
    have h := hi.equalizer (g := fun x : A => U (star x))
      (h := fun x : A => star (U x)) (by fun_prop) (by fun_prop) (by
        funext r
        simp only [Function.comp_apply, ← map_star, hU])
    exact congrFun h a
  exact { U.toLinearEquiv with map_mul' := hmul, map_star' := hstar }

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem starAlgEquivOfDenseNorm_apply
    (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j) (hnorm : ∀ r, ‖j r‖ = ‖i r‖) (r : R) :
    starAlgEquivOfDenseNorm i j hi hj hnorm (i r) = j r :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r

def starAlgEquivOfFaithfulMoments (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) : A ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDenseNorm i j hi hj
    (norm_eq_of_faithful_moments i j hi hj f g htr hf hg)

@[simp] theorem starAlgEquivOfFaithfulMoments_apply (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (r : R) :
    starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg (i r) = j r :=
  starAlgEquivOfDenseNorm_apply ..

theorem starAlgEquivOfFaithfulMoments_preserves (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (a : A) :
    g (starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg a) = f a := by
  let U := starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg
  have h := hi.equalizer (g := fun x : A => positiveCLM g (U x))
    (h := fun x : A => positiveCLM f x) (by fun_prop) (by fun_prop) (by
      funext r
      simp only [Function.comp_apply, U, starAlgEquivOfFaithfulMoments_apply,
        positiveCLM_apply, htr])
  exact congrFun h a

end FaithfulMoments

section MomentEquivalences

open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

private theorem hnn_generators_star (φ : A →⋆ₐ[ℂ] B) (v : Bool → B)
    (hv : ∀ i, star (v i) = v (!i)) :
    star (Set.range φ ∪ Set.range v) ⊆ Set.range φ ∪ Set.range v := by
  intro x hx
  have hh : star x ∈ Set.range φ ∪ Set.range v := Set.mem_star.mp hx
  rcases hh with ⟨a,ha⟩ | ⟨i,hi⟩
  · left
    exact ⟨star a, by rw [map_star,ha,star_star]⟩
  · right
    exact ⟨!i, by rw [← hv,hi,star_star]⟩

theorem hnn_moments_equal
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →L[ℂ] ℂ) (g : C →L[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))) :
    f (z.val.1) = g (z.val.2) := by
  let η := φ.prod ψ
  let t : Bool → B × C := fun i => (v i,w i)
  have ht : ∀ i, star (t i) = t (!i) := fun i => Prod.ext (hv i) (hw i)
  have hrt : ∀ i a, t i*η a*t (!i) = t i*η (center i a)*t (!i) + η (r i a) :=
    fun i a => Prod.ext (hrv i a) (hrw i a)
  have hz : z.val ∈ Algebra.adjoin ℂ (Set.range η ∪ Set.range t) := by
    have hh := z.property
    change z.val ∈ (StarAlgebra.adjoin ℂ (Set.range η ∪ Set.range t)).toSubalgebra at hh
    rw [StarAlgebra.adjoin_toSubalgebra, Set.union_eq_self_of_subset_right
      (hnn_generators_star η t ht)] at hh
    exact hh
  have hspan := adjoin_le_hnnWordSpan η t K center r hc hrt hz
  have eval_proj (u : HNNWord A) : (u.eval η t).1 = u.eval φ v ∧
      (u.eval η t).2 = u.eval ψ w := by
    induction u with
    | single i a => exact ⟨rfl,rfl⟩
    | cons i a u ih =>
      change v i*φ a*(u.eval η t).1 = _ ∧ w i*ψ a*(u.eval η t).2 = _
      rw [ih.1,ih.2]
      exact ⟨rfl,rfl⟩
  generalize hzv : z.val = x at hspan ⊢
  clear hzv
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨u,a,hu,rfl⟩
    · exact hbase a
    · change f (φ a*(u.eval η t).1) = g (ψ a*(u.eval η t).2)
      rw [(eval_proj u).1,(eval_proj u).2]
      exact hred u a hu
  | zero => simp only [Prod.fst_zero,Prod.snd_zero,map_zero]
  | add x y hx hy ix iy => simp only [Prod.fst_add,Prod.snd_add,map_add,ix,iy]
  | smul c x hx ix =>
    change f (c • x.1) = g (c • x.2)
    rw [map_smul,map_smul,ix]

theorem hnn_pair_fst_dense (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    DenseRange ((StarAlgHom.fst ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := ((StarAlgHom.fst ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype).range) ?_ hx
  rintro y (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · refine ⟨⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩,rfl⟩
  · refine ⟨⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩,rfl⟩

theorem hnn_pair_snd_dense (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    DenseRange ((StarAlgHom.snd ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := ((StarAlgHom.snd ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype).range) ?_ hx
  rintro y (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · refine ⟨⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩,rfl⟩
  · refine ⟨⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩,rfl⟩

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (hf : ∀ a : B, f (star a*a) = 0 → a = 0)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0)
    (hB : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B))
    (hC : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C))

def hnnFaithfulEquiv : B ≃⋆ₐ[ℂ] C :=
  starAlgEquivOfFaithfulMoments
    ((StarAlgHom.fst ℂ B C).comp (StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype)
    ((StarAlgHom.snd ℂ B C).comp (StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype)
    (hnn_pair_fst_dense φ ψ v w hB) (hnn_pair_snd_dense φ ψ v w hC) f g
    (hnn_moments_equal φ ψ v w hv hw K center r hc hrv hrw
      (positiveCLM f) (positiveCLM g) hbase hred) hf hg

theorem hnnFaithfulEquiv_base (a : A) :
    hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC
      (φ a) = ψ a := by
  let z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i))) :=
    ⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩
  unfold hnnFaithfulEquiv
  exact starAlgEquivOfFaithfulMoments_apply _ _ _ _ _ _ _ _ _ z

theorem hnnFaithfulEquiv_letter (i : Bool) :
    hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC
      (v i) = w i := by
  let z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i))) :=
    ⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩
  unfold hnnFaithfulEquiv
  exact starAlgEquivOfFaithfulMoments_apply _ _ _ _ _ _ _ _ _ z

theorem hnnFaithfulEquiv_preserves (b : B) :
    g (hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC b)
      = f b :=
  starAlgEquivOfFaithfulMoments_preserves _ _ _ _ _ _ _ _ _ b
end MomentEquivalences

section HNNRestriction

open Topology
open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

def hnnGenerated (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) : StarSubalgebra ℂ C :=
  (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w)).topologicalClosure

theorem hnnGenerated_isClosed (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    IsClosed (hnnGenerated ψ w : Set C) := isClosed_closure
attribute [local instance] hnnGenerated_isClosed

def hnnGeneratedBase (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) : A →⋆ₐ[ℂ] hnnGenerated ψ w :=
  ψ.codRestrict _ (fun a => subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)))

def hnnGeneratedLetter (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (i : Bool) : hnnGenerated ψ w :=
  ⟨w i,subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩))⟩

theorem hnnGenerated_dense (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    Dense (StarAlgebra.adjoin ℂ
      (Set.range (hnnGeneratedBase ψ w) ∪ Set.range (hnnGeneratedLetter ψ w)) :
        Set (hnnGenerated ψ w)) := by
  let R := StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w)
  let T := StarAlgebra.adjoin ℂ
    (Set.range (hnnGeneratedBase ψ w) ∪ Set.range (hnnGeneratedLetter ψ w))
  have hm : T.map (hnnGenerated ψ w).subtype = R := by
    rw [StarAlgHom.map_adjoin]
    apply congrArg (StarAlgebra.adjoin ℂ)
    ext x
    constructor
    · rintro ⟨y,(⟨a,rfl⟩ | ⟨i,rfl⟩),rfl⟩
      · exact Or.inl ⟨a,rfl⟩
      · exact Or.inr ⟨i,rfl⟩
    · rintro (⟨a,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨hnnGeneratedBase ψ w a,Or.inl ⟨a,rfl⟩,rfl⟩
      · exact ⟨hnnGeneratedLetter ψ w i,Or.inr ⟨i,rfl⟩,rfl⟩
  have hd : DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure R)) := by
    exact (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  apply hd.mono
  rintro x ⟨y,rfl⟩
  have hy : y.val ∈ T.map (hnnGenerated ψ w).subtype := by
    rw [hm]
    exact y.property
  obtain ⟨z,hz,hzy⟩ := hy
  have he : z = Set.inclusion (StarSubalgebra.le_topologicalClosure R) y :=
    Subtype.ext hzy
  exact he ▸ hz

section Trace
variable [PartialOrder C] [StarOrderedRing C]

def restrictPositive (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ) : S →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (g.toLinearMap.comp S.subtype.toAlgHom.toLinearMap)
    (fun x hx => g.map_nonneg (by
      let π : S →⋆ₙ+* C :=
        { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl,
          map_mul' := fun _ _ => rfl, map_star' := fun _ => rfl }
      have h := π.map_le_map_of_map_star hx
      exact h))

@[simp] theorem restrictPositive_apply (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ) (z : S) :
    restrictPositive S g z = g z.val := rfl

theorem restrictPositive_faithful (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0) (z : S)
    (hz : restrictPositive S g (star z*z) = 0) : z = 0 :=
  Subtype.ext (hg z.val hz)
end Trace

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

theorem exists_hnnRestriction
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (hf : ∀ a : B, f (star a*a) = 0 → a = 0)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0)
    (hB : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    ∃ F : B →⋆ₐ[ℂ] C, Function.Injective F ∧
      (∀ a, F (φ a) = ψ a) ∧ (∀ i, F (v i) = w i) ∧
      (∀ b, g (F b) = f b) ∧ F.range = hnnGenerated ψ w := by
  let S := hnnGenerated ψ w
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let Ψ := hnnGeneratedBase ψ w
  let ω := hnnGeneratedLetter ψ w
  let G := restrictPositive S g
  have hω : ∀ i, star (ω i) = ω (!i) := fun i => Subtype.ext (hw i)
  have hrω : ∀ i a, ω i*Ψ a*ω (!i) = ω i*Ψ (center i a)*ω (!i) + Ψ (r i a) :=
    fun i a => Subtype.ext (hrw i a)
  have hGb : ∀ a, f (φ a) = G (Ψ a) := hbase
  have heval (u : HNNWord A) : (u.eval Ψ ω).val = u.eval ψ w := by
    induction u with
    | single i a => rfl
    | cons i a u ih =>
      change w i*ψ a*(u.eval Ψ ω).val = w i*ψ a*u.eval ψ w
      rw [ih]
  have hGr : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = G (Ψ a*u.eval Ψ ω) := by
    intro u a hu
    change f (φ a*u.eval φ v) = g (ψ a*(u.eval Ψ ω).val)
    rw [heval]
    exact hred u a hu
  have hGf : ∀ a : S, G (star a*a) = 0 → a = 0 := restrictPositive_faithful S g hg
  let e := hnnFaithfulEquiv φ Ψ v ω hv hω K center r hc hrv hrω f G
    hGb hGr hf hGf hB (hnnGenerated_dense ψ w)
  refine ⟨S.subtype.comp e.toStarAlgHom, Subtype.val_injective.comp e.injective, ?_, ?_, ?_, ?_⟩
  · intro a
    exact congrArg Subtype.val (hnnFaithfulEquiv_base φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) a)
  · intro i
    exact congrArg Subtype.val (hnnFaithfulEquiv_letter φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) i)
  · intro b
    exact hnnFaithfulEquiv_preserves φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) b
  · ext z
    constructor
    · rintro ⟨b,rfl⟩
      exact (e b).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩,congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)⟩

end HNNRestriction

section WordSpans

open Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

def hnnReducedSpan : Submodule ℂ B :=
  Submodule.span ℂ {z | ∃ (w : HNNWord A) (a : A), w.Reduced K ∧ z = φ a*w.eval φ v}

theorem hnnWordSpan_center_mem (E : B →L[ℂ] A) (hbase : ∀ a, E (φ a) = a)
    (hred : ∀ (w : HNNWord A) (a : A), w.Reduced K → E (φ a*w.eval φ v) = 0)
    {x : B} (hx : x ∈ hnnWordSpan φ v K) : x-φ (E x) ∈ hnnReducedSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨w,a,hw,rfl⟩
    · simpa only [hbase,sub_self] using (hnnReducedSpan φ v K).zero_mem
    · rw [hred w a hw,map_zero,sub_zero]
      exact Submodule.subset_span ⟨w,a,hw,rfl⟩
  | zero => simpa only [map_zero,sub_self] using (hnnReducedSpan φ v K).zero_mem
  | add x y hx hy ix iy =>
    simpa only [map_add,add_sub_add_comm] using (hnnReducedSpan φ v K).add_mem ix iy
  | smul c x hx ix =>
    simpa only [map_smul,smul_sub] using (hnnReducedSpan φ v K).smul_mem c ix

theorem hnnWordSpan_dense (hv : ∀ i, star (v i) = v (!i))
    (center r : Bool → A → A) (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    Dense (hnnWordSpan φ v K : Set B) := by
  apply hd.mono
  intro z hz
  apply adjoin_le_hnnWordSpan φ v K center r hc hr
  change z ∈ (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v)).toSubalgebra at hz
  have hs : star (Set.range φ ∪ Set.range v) ⊆ Set.range φ ∪ Set.range v := by
    intro x hx
    have hh : star x ∈ Set.range φ ∪ Set.range v := Set.mem_star.mp hx
    rcases hh with ⟨a,ha⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨star a,by rw [map_star,ha,star_star]⟩
    · exact Or.inr ⟨!i,by rw [← hv,hi,star_star]⟩
  rwa [StarAlgebra.adjoin_toSubalgebra,Set.union_eq_self_of_subset_right hs] at hz

theorem hnn_kernel_mem_closure_reducedSpan (E : B →L[ℂ] A)
    (hbase : ∀ a, E (φ a) = a)
    (hred : ∀ (w : HNNWord A) (a : A), w.Reduced K → E (φ a*w.eval φ v) = 0)
    (hd : Dense (hnnWordSpan φ v K : Set B)) {x : B} (hx : E x = 0) :
    x ∈ closure (hnnReducedSpan φ v K : Set B) := by
  let P : B →L[ℂ] B := ContinuousLinearMap.id ℂ B - (starAlgHomCLM φ).comp E
  have hP : ∀ y, P y ∈ closure (hnnReducedSpan φ v K : Set B) := by
    intro y
    have hall : closure (hnnWordSpan φ v K : Set B) ⊆
        P ⁻¹' closure (hnnReducedSpan φ v K : Set B) :=
      closure_minimal (fun z hz => subset_closure (hnnWordSpan_center_mem φ v K E hbase hred hz))
        (isClosed_closure.preimage P.continuous)
    exact hall (hd y)
  simpa only [P,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,starAlgHomCLM_apply,hx,map_zero,sub_zero] using hP x

end WordSpans

open Topology
variable {A B C D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra C] [CStarAlgebra D]

theorem hnn_starAdjoin_le_wordSpan (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C)
    (hw : ∀ i, star (w i) = w (!i)) (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a)) :
    (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C) ⊆ hnnWordSpan ψ w K := by
  intro z hz
  apply adjoin_le_hnnWordSpan ψ w K center r hc hr
  change z ∈ (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w)).toSubalgebra at hz
  have hs : star (Set.range ψ ∪ Set.range w) ⊆ Set.range ψ ∪ Set.range w := by
    intro x hx
    have hh : star x ∈ Set.range ψ ∪ Set.range w := Set.mem_star.mp hx
    rcases hh with ⟨a,ha⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨star a,by rw [map_star,ha,star_star]⟩
    · exact Or.inr ⟨!i,by rw [← hw,hi,star_star]⟩
  rwa [StarAlgebra.adjoin_toSubalgebra,Set.union_eq_self_of_subset_right hs] at hz

theorem expectation_mem_smaller_base
    (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι) (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C)
    (hw : ∀ i, star (w i) = w (!i)) (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (E : C →L[ℂ] B) (hbase : ∀ a, E (ψ a) = ι a)
    (hred : ∀ (u : HNNWord A) a, u.Reduced K → E (ψ a*u.eval ψ w) = 0)
    {x : C} (hx : x ∈ hnnGenerated ψ w) : E x ∈ ι.range := by
  have hclosed : IsClosed (ι.range : Set B) :=
    (NonUnitalStarAlgHom.isometry ι hι).isClosedEmbedding.isClosed_range
  have hspan : ∀ z ∈ hnnWordSpan ψ w K, E z ∈ ι.range := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨a,rfl⟩ | ⟨u,a,hu,rfl⟩
      · rw [hbase]; exact ⟨a,rfl⟩
      · rw [hred u a hu]; exact ι.range.zero_mem
    | zero => rw [map_zero]; exact ι.range.zero_mem
    | add z t hz ht iz it => rw [map_add]; exact ι.range.add_mem iz it
    | smul c z hz iz =>
      rw [map_smul]
      exact ι.range.toSubalgebra.toSubmodule.smul_mem c iz
  exact closure_minimal
    (fun z hz => hspan z (hnn_starAdjoin_le_wordSpan ψ w hw K center r hc hr hz))
    (hclosed.preimage E.continuous) hx

theorem HNNWord.eval_hom (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C) (F : B →⋆ₐ[ℂ] C)
    (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i) (u : HNNWord A) :
    F (u.eval φ v) = u.eval ψ w := by
  induction u with
  | single i a => simp only [HNNWord.eval,map_mul,hbase,hletter]
  | cons i a u ih => simp only [HNNWord.eval,map_mul,hbase,hletter,ih]

theorem hnn_expectation_intertwines
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (ι : A →⋆ₐ[ℂ] D)
    (v : Bool → B) (w : Bool → C) (F : B →⋆ₐ[ℂ] C)
    (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i)
    (hv : ∀ i, star (v i) = v (!i)) (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (E : B →L[ℂ] A) (G : C →L[ℂ] D)
    (hE : ∀ a, E (φ a) = a) (hG : ∀ a, G (ψ a) = ι a)
    (hEr : ∀ (u : HNNWord A) a, u.Reduced K → E (φ a*u.eval φ v) = 0)
    (hGr : ∀ (u : HNNWord A) a, u.Reduced K → G (ψ a*u.eval ψ w) = 0)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) (b : B) :
    G (F b) = ι (E b) := by
  have hd' := hnnWordSpan_dense φ v K hv center r hc hr hd
  have hs : ∀ z ∈ hnnWordSpan φ v K, G (F z) = ι (E z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨a,rfl⟩ | ⟨u,a,hu,rfl⟩
      · rw [hbase,hG,hE]
      · rw [map_mul,hbase,HNNWord.eval_hom φ ψ v w F hbase hletter u,
          hGr u a hu,hEr u a hu,map_zero]
    | zero => simp only [map_zero]
    | add x y hx hy ix iy => simp only [map_add,ix,iy]
    | smul c x hx ix => simp only [map_smul,ix]
  exact (isClosed_eq (G.continuous.comp (starAlgHomCLM F).continuous)
    ((starAlgHomCLM ι).continuous.comp E.continuous)).closure_subset_iff.mpr hs (hd' b)

end NaimarkZFC

end

end OAI
