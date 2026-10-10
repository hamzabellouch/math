import Mathlib
import OAI.Analysis.FreeWords.ScalarFreeApprox
import OAI.Analysis.FreeWords.SurjectiveExponentialLift
import OAI.Analysis.FreeWords.UnitaryTraceContinuity

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKLocalPatching

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H}

local instance freeSurjectiveImageConcreteOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance freeSurjectiveImageConcretePreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance freeSurjectiveImageConcreteLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance freeSurjectiveImageConcreteSOR : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem finite_free_in_surjective_image (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hF : IsFactor M) (hD : IsDiffuse M)
    (φ : A →⋆ₐ[ℂ] ConcreteAlgebra M) (hsur : Function.Surjective φ)
    (K : Finset ℤ) (F : Finset (List (ℤ × ConcreteAlgebra M)))
    (hFne : ∀ w∈F, w≠[]) (hcenter : ∀ w∈F, ∀ z∈w, z.1≠0 ∧ τ.map z.2=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ v : unitary A, let u := Unitary.map (StarMonoidHom.ofClass φ) v
      (∀ k∈K, k≠0 → ‖τ.map ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ.map ((w.map (fun z => ((u^z.1).val)*z.2)).prod)‖<ε) := by
  classical
  obtain ⟨u,huK,huF⟩ := finite_scalar_free_approximation M τ hF hD K F hFne hcenter (ε/2) (half_pos hε)
  choose v hv using (fun j : ℕ => unitary_dense_image M φ hsur u (((j:ℝ)+1)⁻¹) (by positivity))
  let f (j : ℕ) := Unitary.map (StarMonoidHom.ofClass φ) (v j)
  have hf : Tendsto (fun j => gnsVector (tracePositive τ) (f j).val) atTop
      (𝓝 (gnsVector (tracePositive τ) u.val)) := by
    apply (tendsto_gns_iff τ).mpr
    have hb (j : ℕ) : traceNorm τ ((f j).val-u.val) ≤ ((j:ℝ)+1)⁻¹ := by
      apply (traceNorm_le_norm τ _).trans
      rw [norm_sub_rev]
      exact (hv j).le
    apply squeeze_zero (fun j => traceNorm_nonneg τ _) hb
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hKevent : ∀ᶠ j in atTop, ∀ k∈K, k≠0 → ‖τ.map (((f j)^k).val)‖<ε := by
    apply (Filter.eventually_all_finset K).mpr
    intro k hk
    by_cases hk0 : k=0
    · exact Eventually.of_forall (fun _ h => (h hk0).elim)
    · have ht := (tendsto_gns_trace τ (tendsto_gns_unitary_zpow τ hf k)).norm
      have hh := (tendsto_order.mp ht).2 ε ((huK k hk hk0).trans (half_lt_self hε))
      filter_upwards [hh] with j hj
      exact fun _ => hj
  have hFevent : ∀ᶠ j in atTop, ∀ w∈F,
      ‖τ.map ((w.map (fun z => (((f j)^z.1).val)*z.2)).prod)‖<ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro w hw
    have ht := (tendsto_gns_trace τ (tendsto_gns_unitary_word τ hf w)).norm
    exact (tendsto_order.mp ht).2 ε ((huF w hw).trans (half_lt_self hε))
  obtain ⟨j,hjK,hjF⟩ := (hKevent.and hFevent).exists
  exact ⟨v j,hjK,hjF⟩

end

end KKVariableUltra
end

end OAI
