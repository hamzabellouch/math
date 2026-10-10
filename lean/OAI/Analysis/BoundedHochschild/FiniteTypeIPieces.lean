import OAI.Analysis.BoundedHochschild.HomogeneousCornerTransport
import OAI.Analysis.BoundedHochschild.FiniteTracialDecomposition

namespace OAI

/-! Existence of finite homogeneous central pieces in finite type I algebras. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  obtain ⟨c, hc⟩ := exists_central_support e hp.1
  have hc0 : c ≠ 0 := fun h => hp0 ((hc.eq_zero_iff hp.1).mpr h)
  let eC := cornerPredualEquiv c hc.1.1 e
  let τC := cornerTrace c hc.1.1 τ
  have hpC := projectionInCorner_abelian hc.1.1 hp hc.2.1
  have hpC0 : projectionInCorner hc.1.1 hp.1 hc.2.1 ≠ 0 :=
    fun h => hp0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hq0, hhom⟩ := exists_homogeneous_piece_of_full_abelian_trace eC τC
    (cornerTrace_tracial c hc.1.1 τ htr) (cornerTrace_faithful c hc.1.1 τ hfaith hc0)
    hpC hpC0 (centralSupport_in_corner hc.1.1 (fun a => (hc.1.2 a).eq) hp.1 hc)
  exact ⟨(q : M), ⟨corner_projection_coe c hc.1.1 hq.1,
    fun a => centralCorner_central hc.1.1 (fun a => (hc.1.2 a).eq) q
      (fun b => (hq.2 b).eq) a⟩,
    (fun h => hq0 (Subtype.ext h)), homogeneousCorner_to_ambient hc.1.1 q hhom⟩

theorem finite_typeI_homogeneous_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M))
    {z : M} (hz : IsStarProjection z) (hzc : ∀ a : M, z * a = a * z) (hz0 : z ≠ 0) :
    ∃ q : M, CentralProjection q ∧ q ≤ z ∧ q ≠ 0 ∧ HomogeneousTypeICorner q := by
  obtain ⟨c, hc, hcc, hcz, hc0, hstate⟩ :=
    exists_central_normal_state_subprojection e hz hzc hz0
  obtain ⟨p, hp, hpc, hp0⟩ := hI.2 c ⟨hc, fun a => hcc a⟩ hc.le_one hc0
  let eC := cornerPredualEquiv c hc e
  have hfinC : FiniteAlgebra (Corner c hc) :=
    (finiteCorner_iff c hc).mp (finiteCorner_of_finiteAlgebra hfinite c hc)
  obtain ⟨ψ, hψ, hψ1, hfaithψ⟩ := central_faithful_state_on_corner e hc hcc hstate
  obtain ⟨τ, _hτ, _hτ1, htr, hfaith⟩ :=
    faithful_normal_trace_of_center_state eC hfinC ψ hψ hψ1 hfaithψ
  have hpC := projectionInCorner_abelian hc hp hpc
  have hpC0 : projectionInCorner hc hp.1 hpc ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hq0, hhom⟩ := exists_homogeneous_piece_of_abelian_trace eC τ htr hfaith hpC hpC0
  refine ⟨(q : M), ⟨corner_projection_coe c hc hq.1,
    fun a => centralCorner_central hc hcc q (fun b => (hq.2 b).eq) a⟩,
    (corner_projection_le c hc hq.1).trans hcz,
    (fun h => hq0 (Subtype.ext h)), homogeneousCorner_to_ambient hc q hhom⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
