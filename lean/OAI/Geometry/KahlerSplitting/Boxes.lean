import OAI.Geometry.KahlerSplitting.Grid

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
namespace UniversalCoverSplitting
open scoped Manifold ContDiff
open Set

def IsBox {n r₁ r₂ : ℕ} {X : ComplexManifold n}
    (S : HolomorphicSplitting X r₁ r₂) (U : Set (ℂ × ℂ))
    (f : ℂ × ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U ∧
  ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1, 0)) =
      mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1, 0) ∧
    S.projection (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0, 1)) = 0

def hartogsFigure (A : (ℂ × ℂ) ≃ᵃ[ℂ] (ℂ × ℂ)) (e a c b : ℝ) : Set (ℂ × ℂ) :=
  {z | (‖(A z).1‖ < e ∧ ‖(A z).2‖ < b) ∨
    (‖(A z).1‖ < a ∧ c < ‖(A z).2‖ ∧ ‖(A z).2‖ < b)}

def hartogsEnvelope (A : (ℂ × ℂ) ≃ᵃ[ℂ] (ℂ × ℂ)) (a b : ℝ) : Set (ℂ × ℂ) :=
  {z | ‖(A z).1‖ < a ∧ ‖(A z).2‖ < b}

def HartogsBoxExtension {n r₁ r₂ : ℕ} {X : ComplexManifold n}
    (S : HolomorphicSplitting X r₁ r₂) : Prop :=
  ∀ (A : (ℂ × ℂ) ≃ᵃ[ℂ] (ℂ × ℂ)) (e a c b : ℝ),
    0 < e → e < a → 0 < c → c < b →
    ∀ f : ℂ × ℂ → X.Carrier, IsBox S (hartogsFigure A e a c b) f →
      ∃ F : ℂ × ℂ → X.Carrier,
        IsBox S (hartogsEnvelope A a b) F ∧
        EqOn F f (hartogsFigure A e a c b) ∧
        ∀ G : ℂ × ℂ → X.Carrier,
          IsBox S (hartogsEnvelope A a b) G →
          EqOn G f (hartogsFigure A e a c b) → EqOn G F (hartogsEnvelope A a b)

section ProjectionEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixed_direction_identity (P : E →L[ℂ] E) (D : (ℂ × ℂ) →L[ℂ] E)
    (h₁ : P (D (1, 0)) = D (1, 0)) (h₂ : P (D (0, 1)) = 0)
    (a₁ a₂ b₁ b₂ : ℂ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    D (a₁, a₂) = (a₁ / b₁) • P (D (b₁, b₂)) +
      (a₂ / b₂) • ((ContinuousLinearMap.id ℂ E - P) (D (b₁, b₂))) := by
  have split (c₁ c₂ : ℂ) : D (c₁, c₂) = c₁ • D (1, 0) + c₂ • D (0, 1) := by
    calc
      D (c₁, c₂) = D (c₁ • (1, 0) + c₂ • (0, 1)) := by congr 1; ext <;> simp
      _ = c₁ • D (1, 0) + c₂ • D (0, 1) := by simp only [map_add, map_smul]
  rw [split a₁ a₂, split b₁ b₂]
  simp only [map_add, map_smul, h₁, h₂, smul_zero, add_zero,
    sub_apply, ContinuousLinearMap.id_apply]
  simp only [sub_self, sub_zero, smul_zero, zero_add, smul_smul,
    div_mul_cancel₀ _ hb₁, div_mul_cancel₀ _ hb₂]

theorem mixed_direction_norm_le (P : E →L[ℂ] E) (D : (ℂ × ℂ) →L[ℂ] E)
    (h₁ : P (D (1, 0)) = D (1, 0)) (h₂ : P (D (0, 1)) = 0)
    (a₁ a₂ b₁ b₂ : ℂ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    ‖D (a₁, a₂)‖ ≤
      (‖a₁ / b₁‖ * ‖P‖ + ‖a₂ / b₂‖ * ‖ContinuousLinearMap.id ℂ E - P‖) *
        ‖D (b₁, b₂)‖ := by
  calc
    ‖D (a₁, a₂)‖ = ‖(a₁ / b₁) • P (D (b₁, b₂)) +
        (a₂ / b₂) • ((ContinuousLinearMap.id ℂ E - P) (D (b₁, b₂)))‖ := by
      rw [mixed_direction_identity P D h₁ h₂ a₁ a₂ b₁ b₂ hb₁ hb₂]
    _ ≤ ‖(a₁ / b₁) • P (D (b₁, b₂))‖ +
        ‖(a₂ / b₂) • ((ContinuousLinearMap.id ℂ E - P) (D (b₁, b₂)))‖ := norm_add_le _ _
    _ = ‖a₁ / b₁‖ * ‖P (D (b₁, b₂))‖ +
        ‖a₂ / b₂‖ * ‖(ContinuousLinearMap.id ℂ E - P) (D (b₁, b₂))‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ‖a₁ / b₁‖ * (‖P‖ * ‖D (b₁, b₂)‖) +
        ‖a₂ / b₂‖ * (‖ContinuousLinearMap.id ℂ E - P‖ * ‖D (b₁, b₂)‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (P.le_opNorm _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.id ℂ E - P).le_opNorm _)
          (norm_nonneg _))
    _ = _ := by ring

end ProjectionEstimate
end UniversalCoverSplitting

noncomputable section
open Set Topology Filter Metric
namespace UniversalCoverSplitting
section CompactQuadratic
variable {B E : Type*} [TopologicalSpace B] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_operator_bound {K : Set B} (hK : IsCompact K)
    (Q : B → E → ℝ) (P : B → E →L[ℝ] E)
    (hQ : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) (K ×ˢ univ))
    (hP : ContinuousOn P K)
    (hpos : ∀ x ∈ K, ∀ u, u ≠ 0 → 0 < Q x u)
    (hhom : ∀ x ∈ K, ∀ (r : ℝ) u, Q x (r • u) = r ^ 2 * Q x u) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u, Q x (P x u) ≤ C * Q x u := by
  let L : Set (B × E) := K ×ˢ sphere 0 1
  have hL : IsCompact L := hK.prod (isCompact_sphere 0 1)
  have hQL : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) L :=
    hQ.mono (prod_mono_right (subset_univ _))
  have hnum : ContinuousOn (fun p : B × E ↦ Q p.1 (P p.1 p.2)) L := by
    apply hQ.comp
      (continuousOn_fst.prodMk ((hP.comp continuousOn_fst (fun _ h ↦ h.1)).clm_apply
        continuousOn_snd))
    exact fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hden : ∀ p ∈ L, Q p.1 p.2 ≠ 0 := by
    intro p hp
    apply ne_of_gt (hpos p.1 hp.1 p.2 _)
    intro he
    have hn : ‖p.2‖ = (1:ℝ) := by simpa using hp.2
    simp [he] at hn
  obtain ⟨C,hC⟩ := hL.bddAbove_image (hnum.div hQL hden)
  refine ⟨max C 1, by positivity, fun x hx u ↦ ?_⟩
  have hzero : Q x 0 = 0 := by simpa using hhom x hx 0 (0:E)
  by_cases hu : u = 0
  · simp [hu,hzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hv : v ∈ sphere (0:E) 1 := by simpa using hvnorm
  have hb : Q x (P x v) / Q x v ≤ max C 1 :=
    (hC ⟨(x,v),⟨hx,hv⟩,rfl⟩).trans (le_max_left _ _)
  have hvpos : 0 < Q x v := hpos x hx v (by intro hh; simp [hh] at hvnorm)
  have hquad : Q x (P x v) ≤ max C 1 * Q x v := (div_le_iff₀ hvpos).mp hb
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    Q x (P x u) = ‖u‖ ^ 2 * Q x (P x v) := by
      conv_lhs => rw [← huv, map_smul]
      exact hhom x hx ‖u‖ (P x v)
    _ ≤ ‖u‖ ^ 2 * (max C 1 * Q x v) := mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
    _ = max C 1 * Q x u := by
      have hs : Q x u = ‖u‖ ^ 2 * Q x v := by rw [← hhom x hx ‖u‖ v, huv]
      rw [hs]
      ring

end CompactQuadratic
end UniversalCoverSplitting
end
end
end

end OAI
