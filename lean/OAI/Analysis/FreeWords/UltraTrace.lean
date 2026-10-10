import Mathlib

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[instance_reducible] def seqOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

attribute [local instance] KKUltraTrace.seqOrder

omit [PartialOrder A] [StarOrderedRing A] in
theorem seqSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKUltraTrace.seqSOR

def ultraTraceValue (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A) : ℂ :=
  Filter.limUnder (ω : Filter ℕ) (fun j => τ (x j))

theorem tendsto_ultraTraceValue (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A) :
    Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (𝓝 (ultraTraceValue τ ω x)) := by
  obtain ⟨C, hC⟩ := τ.exists_norm_apply_le
  have hb : ∀ j, τ (x j) ∈ Metric.closedBall (0 : ℂ) (C * ‖x‖) := by
    intro j
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (hC _).trans (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) C.coe_nonneg)
  obtain ⟨z, hz, hlim⟩ := (isCompact_closedBall (0 : ℂ) (C * ‖x‖)).ultrafilter_le_nhds'
    (ω.map fun j => τ (x j)) (show Metric.closedBall (0 : ℂ) (C * ‖x‖) ∈
      ω.map (fun j => τ (x j)) from Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall hb))
  exact tendsto_nhds_limUnder ⟨z, hlim⟩

theorem ultraTraceValue_add (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x y : ℕ →ᵇ A) :
    ultraTraceValue τ ω (x + y) = ultraTraceValue τ ω x + ultraTraceValue τ ω y := by
  exact (show Tendsto (fun j => τ ((x + y) j)) (ω : Filter ℕ)
    (𝓝 (ultraTraceValue τ ω x + ultraTraceValue τ ω y)) by
      simpa using (tendsto_ultraTraceValue τ ω x).add (tendsto_ultraTraceValue τ ω y)).limUnder_eq

theorem ultraTraceValue_smul (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (c : ℂ) (x : ℕ →ᵇ A) :
    ultraTraceValue τ ω (c • x) = c • ultraTraceValue τ ω x := by
  exact (show Tendsto (fun j => τ ((c • x) j)) (ω : Filter ℕ)
    (𝓝 (c • ultraTraceValue τ ω x)) by
      simpa using (tendsto_ultraTraceValue τ ω x).const_smul c).limUnder_eq

theorem ultraTraceValue_mono (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) :
    Monotone (ultraTraceValue τ ω) := by
  intro x y hxy
  have heval : ∀ j, x j ≤ y j := by
    obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
    intro j
    have hj := congrArg (fun z : ℕ →ᵇ A => z j) hv
    have hj' : y j - x j = star (v j) * v j := hj
    exact sub_nonneg.mp (hj'.symm ▸ star_mul_self_nonneg (v j))
  exact le_of_tendsto_of_tendsto (tendsto_ultraTraceValue τ ω x)
    (tendsto_ultraTraceValue τ ω y) (Eventually.of_forall fun j => OrderHomClass.mono τ (heval j))

def ultraTrace (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) : (ℕ →ᵇ A) →ₚ[ℂ] ℂ where
  toFun := ultraTraceValue τ ω
  map_add' := ultraTraceValue_add τ ω
  map_smul' := ultraTraceValue_smul τ ω
  monotone' := ultraTraceValue_mono τ ω

@[simp] theorem ultraTrace_one (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (h1 : τ 1 = 1) :
    ultraTrace τ ω 1 = 1 := by
  change Filter.limUnder (ω : Filter ℕ) (fun j => τ ((1 : ℕ →ᵇ A) j)) = 1
  exact (show Tendsto (fun j => τ ((1 : ℕ →ᵇ A) j)) (ω : Filter ℕ) (𝓝 1) by
    simp [h1]).limUnder_eq

theorem ultraTrace_tracial (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) (x y : ℕ →ᵇ A) :
    ultraTrace τ ω (x * y) = ultraTrace τ ω (y * x) := by
  change Filter.limUnder (ω : Filter ℕ) (fun j => τ (x j * y j)) =
    Filter.limUnder (ω : Filter ℕ) (fun j => τ (y j * x j))
  congr 1
  funext j
  exact htr _ _

open scoped InnerProductSpace

def gnsVector (τ : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ τ.toPreGNS.toLinearMap

@[simp] theorem gnsVector_inner (τ : A →ₚ[ℂ] ℂ) (x y : A) :
    ⟪gnsVector τ x, gnsVector τ y⟫_ℂ = τ (star x * y) := by
  change ⟪(τ.toPreGNS x : τ.GNS), (τ.toPreGNS y : τ.GNS)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  rfl

@[simp] theorem gnsStarAlgHom_vector (τ : A →ₚ[ℂ] ℂ) (x y : A) :
    τ.gnsStarAlgHom x (gnsVector τ y) = gnsVector τ (x * y) := by
  change τ.gnsNonUnitalStarAlgHom x (τ.toPreGNS y : τ.GNS) =
    (τ.toPreGNS (x * y) : τ.GNS)
  simp

theorem tracial_gns_zero (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) (x : A) :
    τ.gnsStarAlgHom x = 0 ↔ τ (star x * x) = 0 := by
  constructor
  · intro hx
    have hv : gnsVector τ x = 0 := by
      have he := congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T (gnsVector τ 1)) hx
      simpa only [gnsStarAlgHom_vector, mul_one, zero_apply] using he
    rw [← gnsVector_inner, hv, inner_zero_left]
  · intro hx
    have hvec : ∀ b : A, gnsVector τ (x * b) = 0 := by
      intro b
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [gnsVector_inner]
      apply le_antisymm _ (τ.map_nonneg (star_mul_self_nonneg _))
      calc
        τ (star (x * b) * (x * b)) = τ (x * (b * star b) * star x) := by
          rw [htr (star (x * b)) (x * b), star_mul]
          congr 1
          noncomm_ring
        _ ≤ τ (‖b * star b‖ • (x * star x)) :=
          OrderHomClass.mono τ (CStarAlgebra.star_right_conjugate_le_norm_smul x (b * star b))
        _ = 0 := by simp [← Complex.coe_smul, htr x (star x), hx]
    ext ξ
    induction ξ using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (τ.gnsStarAlgHom x).continuous continuous_const
    | ih b =>
      change τ.gnsStarAlgHom x (gnsVector τ (τ.ofPreGNS b)) = 0
      rw [gnsStarAlgHom_vector]
      exact hvec _

theorem ultraTrace_exists (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ x y : A, τ (x * y) = τ (y * x)) (ω : Ultrafilter ℕ) :
    ∃ T : (ℕ →ᵇ A) →ₚ[ℂ] ℂ,
      (∀ x, T x = ultraTraceValue τ ω x) ∧
      (∀ x, Filter.Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds (T x))) ∧
      T 1 = 1 ∧ (∀ x y, T (x * y) = T (y * x)) ∧
      (∀ x, T.gnsStarAlgHom x = 0 ↔ T (star x * x) = 0) := by
  refine ⟨ultraTrace τ ω, fun _ => rfl, tendsto_ultraTraceValue τ ω,
    ultraTrace_one τ ω h1, ultraTrace_tracial τ ω htr, ?_⟩
  exact tracial_gns_zero _ (ultraTrace_tracial τ ω htr)

end

end KKUltraTrace
end

end OAI
