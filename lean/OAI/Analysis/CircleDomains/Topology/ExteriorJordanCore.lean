import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative
import OAI.Analysis.CircleDomains.Topology.ImageCoreJordan
import OAI.Analysis.CircleDomains.Topology.ClosedJordanCore
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization
import OAI.Analysis.CircleDomains.Modulus.NormalizedLimitEquivalence

namespace OAI

/-! A holomorphic principal exterior injection maps each closed exterior
core to the closed exterior of its image Jordan curve. Schoenflies
identifies the filled Jordan disk. -/
open Set Filter Function Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exterior_closed_core_jordan (hsch : PlanarSchoenflies)
    {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    ∃ H : ℂ ≃ₜ ℂ,
      frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) ∧
      (F '' {z : ℂ | a ≤ ‖z‖})ᶜ = jordanInterior H := by
  have hap : 0 < a := hR.trans ha
  let D : Set ℂ := {z | R < ‖z‖}
  let G : Set Sphere := ((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}
  let T : Fin 1 → ℂ ≃ₜ ℂ := fun _ => roundDiskChart a hap
  let K := closedJordanCore T
  have hD : IsOpen D := isOpen_lt continuous_const continuous_norm
  have hG : IsOpen G := isOpen_finite_domain_with_infty hD
    (R := R+1) (by
      intro z hz
      change R+1 ≤ ‖z‖ at hz
      change R < ‖z‖
      linarith)
  have hconf : IsConformalOn (extendAtInfinity F) G :=
    isConformalOn_extendAtInfinity hD hF
      (fun z hz => holomorphicInjOn_deriv_ne_zero hD hF hi hz) hn
  have hpair : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hKe : K = (((↑) : ℂ → Sphere) '' ball (0 : ℂ) a)ᶜ := by
    simp only [K, closedJordanCore, T, roundDiskChart_interior, iUnion_const]
  have hK : IsCompact K := by
    rw [hKe]
    exact (OnePoint.isOpen_image_coe.mpr isOpen_ball).isClosed_compl.isCompact
  have hKG : K ⊆ G := by
    intro p hp
    rw [hKe] at hp
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      apply Or.inl
      refine ⟨z, ?_, rfl⟩
      have hz : a ≤ ‖z‖ := by
        by_contra hh
        exact hp ⟨z, by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hh, rfl⟩
      exact ha.trans_le hz
  have hreg : closure (interior K) = K := closure_interior_closedJordanCore T hpair
  have hconn : IsPreconnected (interior K) := by
    rw [show K = closedJordanCore T from rfl, interior_closedJordanCore]
    exact (isConnected_openCompletedRegion T hpair).isPreconnected
  have hinf : OnePoint.infty ∈ interior K := by
    rw [show K = closedJordanCore T from rfl, interior_closedJordanCore]
    simp only [openCompletedRegion, T, closedTerminalCap, mem_compl_iff, mem_iUnion]
    rintro ⟨i, z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  let γ : Fin 1 → Circle → ℂ := fun i z => T i (z : ℂ)
  have hγ (i : Fin 1) : Continuous (γ i) := (T i).continuous.comp continuous_subtype_val
  have hγi (i : Fin 1) : Injective (γ i) := (T i).injective.comp Subtype.val_injective
  have hγp : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i) := by
    rw [show K = closedJordanCore T from rfl, frontier_closedJordanCore T hpair]
    congr 1
    funext i
    rw [frontier_jordanInterior_eq_circle_range (T i) (γ i) (by intro z; rfl)]
  obtain ⟨H, hH, _, hfill⟩ := exists_jordan_image_core hsch hG hconf
    (injOn_extendAtInfinity hi) hK hKG hreg hconn hinf rfl γ hγ hγi hγp hfront
  refine ⟨H 0, ?_, ?_⟩
  · have hh := hH 0
    simp only [extendAtInfinity_coe, finiteCoord_coe] at hh
    change frontier (jordanInterior (H 0)) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) at hh
    exact hh
  · have he := congrArg (fun S : Set Sphere => ((↑) : ℂ → Sphere) ⁻¹' S) hfill
    have hpre : ((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity F '' K) =
        F '' {z : ℂ | a ≤ ‖z‖} := by
      ext z
      constructor
      · rintro ⟨p, hp, heq⟩
        cases p using OnePoint.rec with
        | infty => exact (OnePoint.coe_ne_infty z heq.symm).elim
        | coe w =>
          refine ⟨w, ?_, OnePoint.coe_injective heq⟩
          rw [hKe] at hp
          by_contra hh
          exact hp ⟨w, by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hh, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(w : Sphere), ?_, rfl⟩
        rw [hKe]
        rintro ⟨v, hv, heq⟩
        have hvw := OnePoint.coe_injective heq
        subst v
        exact (not_lt_of_ge hw) (by simpa only [mem_ball, dist_zero_right] using hv)
    have hh : (F '' {z : ℂ | a ≤ ‖z‖})ᶜ = ⋃ i, jordanInterior (H i) := by
      simpa only [preimage_compl, hpre, preimage_iUnion,
        OnePoint.coe_injective.preimage_image] using he
    apply hh.trans
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      simpa only [Subsingleton.elim i (0 : Fin 1)] using hi
    · intro hz
      exact ⟨0, hz⟩

end CircleDomainRigidity

end

end OAI
