import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.GeneratedEtaleCoordinates
import OAI.AlgebraicGeometry.Seshadri.Analytic.CoordinateJets
import OAI.AlgebraicGeometry.Seshadri.Analytic.PointCharts

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology ContDiff
open MvPolynomial MaximalSeshadri.AnalyticCoordinates
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

omit [DecidableEq ι] [DecidableEq σ] in
lemma presentation_binary_formallyEtale
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2) :
    (MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))
  let : Algebra (MvPolynomial (Fin 2) ℂ) S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S
  apply formallyEtale_polynomial_of_basis (P.basisKaehler.reindex e)
  intro i
  rw [Module.Basis.reindex_apply, P.basisKaehler_apply]
  change KaehlerDifferential.D ℂ S (P.val (e.symm i)) =
    KaehlerDifferential.D ℂ S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

theorem presentation_analytic_realization [IsDomain S]
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
      (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0),
      q 0 = ρ ∧ Function.Injective (analyticTaylor q hq) ∧
      (∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp (analyticTaylor q hq)) =
        (RingHom.ker ρ)^n) ∧
      ∃ U : Set (ℂ × ℂ), IsOpen U ∧ 0 ∈ U ∧ Set.InjOn q U := by
  classical
  let φ := MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))
  let : Algebra (MvPolynomial (Fin 2) ℂ) S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S :=
    presentation_binary_formallyEtale P e
  let := P.isStandardSmooth
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  let : Algebra.FiniteType (MvPolynomial (Fin 2) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  obtain ⟨q, hq₀, hq, hc⟩ := exists_binary_point_chart P e ρ
  have hcoords : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1) := by
    filter_upwards [hc] with z hz
    intro i
    change q z (φ (X i)) = q 0 (φ (X i)) + _
    simpa only [φ, MvPolynomial.aeval_X, hq₀] using hz i
  refine ⟨q, hq, hq₀, analyticTaylor_injective q hq hcoords, ?_, ?_⟩
  · intro n hn
    simpa only [hq₀] using analyticTaylor_detects_ideal_power q hq hcoords n hn
  · obtain ⟨U, hU, hopen, hzero⟩ := eventually_nhds_iff.mp hc
    refine ⟨U, hopen, hzero, ?_⟩
    intro z hz w hw heq
    have hx := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 1))) heq
    have hy := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 0))) heq
    rw [hU z hz 1, hU w hw 1] at hx
    rw [hU z hz 0, hU w hw 0] at hy
    apply Prod.ext
    · simpa using hx
    · simpa using hy

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
open scoped Topology
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

theorem exists_uniform_analytic_point_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ (q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F))
      (U : Set ({i : ι // i ∉ Set.range P.map} → F)),
      IsOpen U ∧ (fun i => ρ (P.val i.val)) ∈ U ∧
      q (fun i => ρ (P.val i.val)) = ρ ∧
      (∀ z ∈ U, ∀ s : S, AnalyticAt F (fun w => q w s) z) ∧
      (∀ z ∈ U, ∀ i, q z (P.val i.val) = z i) := by
  classical
  obtain ⟨γ, hbase, han, hrel⟩ := exists_analytic_zero_chart P ρ
  obtain ⟨U, hU, hopen, hbaseU⟩ := eventually_nhds_iff.mp
    (hrel.and han.eventually_analyticAt)
  let q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F) := fun z =>
    if h : ∀ i, eval (γ z) (P.relation i) = 0 then
      presentationPoint P.toPresentation (γ z) h else ρ
  have heq (z) (hz : z ∈ U) (s : S) : q z s = eval (γ z) (P.σ s) := by
    simp only [q, dite_eq_left (hU z hz).1.1]
    exact presentationPoint_apply P.toPresentation (γ z) (hU z hz).1.1 s
  refine ⟨q, U, hopen, hbaseU, ?_, ?_, ?_⟩
  · have hzero : ∀ i, eval (γ (fun i => ρ (P.val i.val))) (P.relation i) = 0 := by
      rw [hbase]
      exact evaluation_relations P.toPresentation ρ
    simp only [q, dite_eq_left hzero]
    simpa only [hbase] using presentationPoint_at_point P.toPresentation ρ
  · intro z hz s
    have h := (analyticAt_polynomial_eval (P.σ s) _).comp (hU z hz).2
    apply h.congr
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (heq w hw s).symm
  · intro z hz i
    simp only [q, dite_eq_left (hU z hz).1.1]
    rw [presentationPoint_val]
    exact (hU z hz).1.2 i

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology
open MvPolynomial MaximalSeshadri.AnalyticCoordinates
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

theorem exists_uniform_binary_point_chart
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ)) (U : Set (ℂ × ℂ)),
      IsOpen U ∧ 0 ∈ U ∧ q 0 = ρ ∧
      (∀ z ∈ U, ∀ s : S, AnalyticAt ℂ (fun w => q w s) z) ∧
      (∀ z ∈ U, ∀ i : Fin 2,
        q z (P.val (e.symm i)) = ρ (P.val (e.symm i)) +
          (if i = 0 then z.2 else z.1)) ∧ Set.InjOn q U := by
  obtain ⟨q₀, V, hV, hbaseV, hbase, han, hc⟩ := exists_uniform_analytic_point_chart P ρ
  let α (z : ℂ × ℂ) (i : {i : ι // i ∉ Set.range P.map}) :=
    ρ (P.val i) + (if e i = 0 then z.2 else z.1)
  have hα (z : ℂ × ℂ) : AnalyticAt ℂ α z := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.add analyticAt_const
    by_cases h : e i = 0
    · simpa only [ite_eq_left h] using (analyticAt_snd (𝕜 := ℂ) (p := z))
    · simpa only [ite_eq_right h] using (analyticAt_fst (𝕜 := ℂ) (p := z))
  have hα₀ : α 0 = (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i)) := by
    ext i
    simp [α]
  let U := α ⁻¹' V
  let q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ) := fun z => q₀ (α z)
  have hcoord (z) (hz : z ∈ U) (i : Fin 2) :
      q z (P.val (e.symm i)) = ρ (P.val (e.symm i)) +
        (if i = 0 then z.2 else z.1) := by
    simpa [α, q] using hc (α z) hz (e.symm i)
  refine ⟨q, U, hV.preimage (continuous_iff_continuousAt.mpr
    (fun z => (hα z).continuousAt)), ?_, ?_, ?_, hcoord, ?_⟩
  · change α 0 ∈ V
    simpa only [hα₀] using hbaseV
  · change q₀ (α 0) = ρ
    rw [hα₀, hbase]
  · intro z hz s
    exact (han (α z) hz s).comp (hα z)
  · intro z hz w hw heq
    have hx := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 1))) heq
    have hy := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 0))) heq
    rw [hcoord z hz 1, hcoord w hw 1] at hx
    rw [hcoord z hz 0, hcoord w hw 0] at hy
    exact Prod.ext (by simpa using hx) (by simpa using hy)

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology
open MvPolynomial MaximalSeshadri.AnalyticCoordinates
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

theorem presentation_uniform_analytic_jets [IsDomain S]
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ)) (U : Set (ℂ × ℂ)),
      IsOpen U ∧ 0 ∈ U ∧ q 0 = ρ ∧ Set.InjOn q U ∧
      ∀ z ∈ U, ∃ hq : ∀ s, AnalyticAt ℂ (fun w => q (z + w) s) 0,
        Function.Injective (analyticTaylor (fun w => q (z + w)) hq) ∧
        ∀ n : ℕ, 0 < n → RingHom.ker
          ((formalTrunc n).comp (analyticTaylor (fun w => q (z + w)) hq)) =
          (RingHom.ker (q z))^n := by
  classical
  let φ := MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))
  let : Algebra (MvPolynomial (Fin 2) ℂ) S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S :=
    presentation_binary_formallyEtale P e
  let := P.isStandardSmooth
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  let : Algebra.FiniteType (MvPolynomial (Fin 2) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  obtain ⟨q, U, hU, hzero, hbase, han, hc, hinj⟩ :=
    exists_uniform_binary_point_chart P e ρ
  refine ⟨q, U, hU, hzero, hbase, hinj, ?_⟩
  intro z hz
  have hq : ∀ s, AnalyticAt ℂ (fun w => q (z + w) s) 0 := by
    intro s
    have hz' : AnalyticAt ℂ (fun w => q w s) (z + 0) := by
      simpa only [add_zero] using han z hz s
    exact hz'.comp (show AnalyticAt ℂ (fun w : ℂ × ℂ => z + w) 0 from
      analyticAt_const.add analyticAt_id)
  have hmem : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), z + w ∈ U :=
    (hU.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hz)
  have hcoords : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∀ i : Fin 2,
      q (z + w) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X i)) =
      q (z + 0) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X i)) +
        (if i = 0 then w.2 else w.1) := by
    filter_upwards [hmem] with w hw
    intro i
    change q (z + w) (φ (X i)) = q (z + 0) (φ (X i)) + _
    simp only [φ, MvPolynomial.aeval_X, add_zero]
    rw [hc (z + w) hw i, hc z hz i]
    split_ifs <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  refine ⟨hq, analyticTaylor_injective _ hq hcoords, ?_⟩
  intro n hn
  simpa only [add_zero] using
    analyticTaylor_detects_ideal_power (fun w => q (z + w)) hq hcoords n hn

end
end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
