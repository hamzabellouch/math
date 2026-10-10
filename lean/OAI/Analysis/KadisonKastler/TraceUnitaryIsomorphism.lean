import OAI.Analysis.KadisonKastler.TraceTransferBound
import OAI.Analysis.KadisonKastler.SpectralJordanMap
import OAI.Analysis.KadisonKastler.FactorAnticommuting
import OAI.Analysis.KadisonKastler.FiniteFactorPrime
import OAI.Analysis.KadisonKastler.FaithfulRepresentation
import OAI.Analysis.KadisonKastler.Range

namespace OAI

/-! # The finite-factor isomorphism from boundary unitary images

The unitary image formula determines a continuous unital Jordan map.
The reverse distance gives surjectivity, and the two-by-two matrix
unitaries force its multiplicative orientation.
-/

namespace KadisonKastler

noncomputable section

variable {H E I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {M N : VonNeumannAlgebra H}

/-- A uniformly close unitary-image formula on a trace-dense family
produces a nearby star isomorphism between the finite factors. -/
theorem exists_near_starEquiv_of_traceDense_unitary_images
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    {C : ℝ} (hC : 0 ≤ C)
    (himages : ∀ i, ∃ v : unitary (Algebra N),
      K v = (S : E →L[ℂ] E) (J (ρ i)) ∧
      ‖(v : H →L[ℂ] H) - (ρ i : Algebra M)‖ ≤ C)
    (hsmall : 3 * (2 * C) + (2 * C) ^ 2 < 2)
    (hgap : kkDistance M N + 2 * C < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ a, ‖(θ a : H →L[ℂ] H) - (a : H →L[ℂ] H)‖ ≤ 2 * C * ‖a‖) := by
  obtain ⟨F, hF1, hF, hFU⟩ := exists_continuous_unital_transfer_of_traceDense
    τM τN J K hJ hK hτN ρ hρ S hS1 (fun i => by
      obtain ⟨v, hv, _⟩ := himages i
      exact ⟨v, hv⟩)
  have hgroup (i : I) : ‖(F (ρ i) : H →L[ℂ] H) - (ρ i : Algebra M)‖ ≤ C := by
    obtain ⟨v, hv, hb⟩ := himages i
    have he : F (ρ i) = (v : Algebra N) :=
      traceHilbert_injective K hK ((hF (ρ i)).trans hv.symm)
    simpa only [he] using hb
  have hunit := unitary_transfer_bound_of_traceDense τM τN hτM hτN J K hJ hK
    S F.toLinearMap hF hFU ρ hρ hC hgroup
  have hclose := linear_transfer_norm_sub_le F.toLinearMap hunit
  have he : 0 ≤ 2 * C := by positivity
  have he1 : 2 * C < 1 := by linarith [kkDistance_nonneg M N]
  have hbij : Function.Bijective F := by
    apply bijective_of_close_isometry_and_reverse_gap
      (starAlgHomToContinuousLinearMap M.toStarSubalgebra.subtype)
      (starAlgHomToContinuousLinearMap N.toStarSubalgebra.subtype)
      F (fun _ => rfl) (fun _ => rfl) he he1 hgap hclose
    intro y hy r hr
    obtain ⟨x, hx, hxy⟩ := exists_unitBall_approx
      (M := N) (N := M) (x := (y : H →L[ℂ] H)) ⟨y.property, hy⟩
      (by simpa only [kkDistance_comm N M] using hr)
    exact ⟨⟨x, hx.1⟩, hx.2, hxy⟩
  have hmult := PreservesJordan.multiplicative_of_close_of_II1 hM F.toLinearMap
    M.toStarSubalgebra.subtype.toAlgHom N.toStarSubalgebra.subtype.toAlgHom
    (preservesJordan_of_map_unitary F hF1 hFU) hbij.2 (finiteFactor_isPrimeAlgebra hN)
    he (fun _ => rfl) hclose hsmall
  let φ : Algebra M →⋆ₐ[ℂ] Algebra N :=
    { toFun := F
      map_zero' := map_zero F
      map_add' := map_add F
      map_one' := hF1
      map_mul' := hmult
      commutes' := by
        intro z
        change F (z • 1) = z • 1
        rw [map_smul, hF1]
      map_star' := fun x => (map_star_square_of_map_unitary F hF1 hFU x).1 }
  exact ⟨StarAlgEquiv.ofBijective φ hbij, hF, hclose⟩

end

end KadisonKastler

end OAI
