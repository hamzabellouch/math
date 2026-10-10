import Mathlib
import OAI.Analysis.FreeWords.UnitaryTraceWitnessSupport

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKUltraTrace KKFactorSupport

open scoped ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteConjHull (τ : A →ₚ[ℂ] ℂ) (x : A) : Set τ.GNS :=
  closure (convexHull ℝ (Set.range fun u : unitary A => gnsVector τ (algebraConj u x)))

theorem finite_trace_in_conjugacyHull [FiniteDimensional ℂ A]
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ x y, τ (x*y)=τ (y*x)) (h1 : τ 1=1)
    (hinj : Function.Injective (gnsVector τ))
    (hcenter : ∀ a : A, (∀ b : A, Commute a b) → ∃ c : ℂ, a=c•1)
    (x : A) : gnsVector τ (τ x•1)∈finiteConjHull τ x := by
  let : InnerProductSpace ℝ τ.GNS := InnerProductSpace.rclikeToReal ℂ τ.GNS
  have hconv : Convex ℝ (finiteConjHull τ x) := (convex_convexHull ℝ _).closure
  have hne : (finiteConjHull τ x).Nonempty := by
    refine ⟨gnsVector τ x,subset_closure (subset_convexHull ℝ _ ?_)⟩
    refine ⟨1,?_⟩
    simp only [algebraConj_apply,OneMemClass.coe_one,one_mul,star_one,mul_one]
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne isClosed_closure.isComplete hconv 0
  have hrange : finiteConjHull τ x ⊆ LinearMap.range (gnsVector τ) := by
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨u,rfl⟩; exact ⟨algebraConj u x,rfl⟩
      · exact ((LinearMap.range (gnsVector τ)).restrictScalars ℝ).convex
    · exact (LinearMap.range (gnsVector τ)).closed_of_finiteDimensional
  obtain ⟨a,hav⟩ := hrange hv
  have hmap (u : unitary A) : Set.MapsTo (gnsConj τ htr u)
      (finiteConjHull τ x) (finiteConjHull τ x) := by
    apply KKFactorSupport.mapsTo_hull ((gnsConj τ htr u).restrictScalars ℝ)
    rintro _ ⟨w,rfl⟩
    refine ⟨u*w,?_⟩
    change gnsVector τ (algebraConj (u*w) x)=gnsConj τ htr u (gnsVector τ (algebraConj w x))
    rw [gnsConj_vector]
    congr 1
    simp only [algebraConj_apply,Submonoid.coe_mul,star_mul,mul_assoc]
  have hfixed (u : unitary A) : gnsConj τ htr u v=v :=
    (KKFactorSupport.norm_minimizer_unique hconv hv (hmap u hv) hmin (gnsConj_norm τ htr u v)).symm
  have ha : ∀ b : A, Commute a b := by
    apply KKFactorSupport.commute_all_of_unitary
    intro u
    have he : algebraConj u a=a := by
      apply hinj
      rw [← gnsConj_vector,hav]
      exact hfixed u
    have hh := congrArg (fun z => z*(u:A)) he
    simp only [algebraConj_apply,mul_assoc,Unitary.coe_star_mul_self,mul_one] at hh
    exact hh.symm
  obtain ⟨c,hc⟩ := hcenter a ha
  have htrace : ⟪gnsVector τ 1,v⟫_ℂ=τ x := by
    let φ : τ.GNS →L[ℝ] ℂ := (innerSL ℂ (gnsVector τ 1)).restrictScalars ℝ
    have hc' : Convex ℝ {v | φ v=τ x} := by
      intro a ha b hb c d hc hd hcd
      change φ (c•a+d•b)=τ x
      rw [map_add,map_smul,map_smul,ha,hb,← add_smul,hcd,one_smul]
    have ho : (Set.range fun u : unitary A => gnsVector τ (algebraConj u x)) ⊆
        {v | φ v=τ x} := by
      rintro _ ⟨u,rfl⟩
      change ⟪gnsVector τ 1,gnsVector τ (algebraConj u x)⟫_ℂ=τ x
      rw [gnsVector_inner,star_one,one_mul,trace_algebraConj τ htr]
    exact closure_minimal (convexHull_min ho hc') (isClosed_eq φ.continuous continuous_const) hv
  rw [← hav,gnsVector_inner,star_one,one_mul,hc,map_smul,h1,smul_eq_mul,mul_one] at htrace
  rw [← htrace,← hc]
  exact hav.symm ▸ hv

theorem finite_commutator_witness [FiniteDimensional ℂ A]
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ x y, τ (x*y)=τ (y*x)) (h1 : τ 1=1)
    (hinj : Function.Injective (gnsVector τ))
    (hcenter : ∀ a : A, (∀ b : A, Commute a b) → ∃ c : ℂ, a=c•1)
    (x : A) : ∃ u : unitary A,
      ‖gnsVector τ (x-τ x•1)‖≤2*‖gnsVector τ (x*(u:A)-(u:A)*x)‖ := by
  by_cases hz : ‖gnsVector τ (x-τ x•1)‖=0
  · exact ⟨1,by rw [hz]; positivity⟩
  by_contra! hall
  have hbound : finiteConjHull τ x ⊆
      Metric.closedBall (gnsVector τ x) (‖gnsVector τ (x-τ x•1)‖/2) := by
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        rw [Metric.mem_closedBall,dist_comm,dist_eq_norm,gnsVector_conj_sub_norm τ htr]
        linarith [hall u]
      · exact convex_closedBall _ _
    · exact Metric.isClosed_closedBall
  have hb := hbound (finite_trace_in_conjugacyHull τ htr h1 hinj hcenter x)
  rw [Metric.mem_closedBall,dist_comm,dist_eq_norm,← map_sub] at hb
  exact hz (by have hh:=norm_nonneg (gnsVector τ (x-τ x•1)); linarith)

end

end KKVariableUltra
end

end OAI
