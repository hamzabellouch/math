import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicPolynomialNonzero

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem linear_projection_chart_germ {m N : ℕ} (V : Set (Affine N))
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    ∃ (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N),
      H 0 = F 0 ∧ AnalyticAt ℂ H 0 ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), π (H z - F 0) = z) ∧
      (∀ᶠ y in 𝓝[V] (F 0), H (π (y-F 0)) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), H z ∈ V) := by
  let π := fderiv ℂ G (F 0)
  have hid : π.comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ :=
    ((hG.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm).unique (hasFDerivAt_id 0)
  have hG0 : G (F 0) = 0 := hGF.eq_of_nhds
  let f : Affine m → Affine m := fun z => π (F z-F 0)
  have hf : AnalyticAt ℂ f 0 := (π.analyticAt _).comp (hF.sub analyticAt_const)
  have hf0 : f 0 = 0 := by simp [f]
  have hfd : HasFDerivAt f (ContinuousLinearEquiv.refl ℂ (Affine m) : Affine m →L[ℂ] Affine m) 0 := by
    have hh := π.hasFDerivAt.comp 0 (hF.differentiableAt.hasFDerivAt.sub_const (F 0))
    simpa only [Function.comp_def,hid,ContinuousLinearEquiv.coe_refl] using hh
  obtain ⟨e,he,h0,hea⟩ := analytic_local_inverse hf (ContinuousLinearEquiv.refl ℂ (Affine m)) hfd
  have he0 : e 0 = 0 := by rw [he]; exact hf0
  have hinv0 : e.symm 0 = 0 := by simpa only [he0] using e.left_inv h0
  have htarget : (0 : Affine m) ∈ e.target := by simpa only [he0] using e.map_source h0
  have hean : AnalyticAt ℂ e.symm 0 := by simpa only [hf0] using hea
  have het : Tendsto e.symm (𝓝 (0 : Affine m)) (𝓝 0) := by
    simpa only [ContinuousAt,hinv0] using hean.continuousAt
  let H := F ∘ e.symm
  refine ⟨π,H,by simp only [H,Function.comp_apply,hinv0],?_,?_,?_,het hFV⟩
  · exact (by simpa only [hinv0] using hF : AnalyticAt ℂ F (e.symm 0)).comp hean
  · filter_upwards [e.open_target.mem_nhds htarget] with z hz
    simpa only [H,he,f,Function.comp_apply] using e.right_inv hz
  · have hGs : ∀ᶠ y in 𝓝 (F 0), G y ∈ e.source :=
      hG.continuousAt.preimage_mem_nhds (by simpa only [hG0] using e.open_source.mem_nhds h0)
    filter_upwards [hFG,mem_nhdsWithin_of_mem_nhds hGs] with y hy hys
    have hl := e.left_inv hys
    rw [he] at hl
    have hfy : f (G y) = π (y-F 0) := by simp only [f,hy]
    rw [hfy] at hl
    change F (e.symm (π (y-F 0))) = y
    rw [hl,hy]
end

open Set Filter Topology Metric
open scoped Classical

theorem isSemialgebraic_zeroLocus {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsSemialgebraic (MvPolynomial.zeroLocus ℂ I) := by
  obtain ⟨S,hS⟩ := I.fg_of_isNoetherianRing
  rw [← hS,MvPolynomial.zeroLocus_span]
  apply isSemialgebraic_iff_polynomialSignSet.mpr
  have h : PolynomialSignSet realCoordinates {z : Affine n | ∀ p : S, MvPolynomial.eval z p.val = 0} :=
    PolynomialSignSet.forall_finite _ (fun p =>
      isSemialgebraic_iff_polynomialSignSet.mp (isSemialgebraic_polynomial_zero p.val))
  convert h using 1
  ext z
  change (∀ p ∈ (S : Set (MvPolynomial (Fin n) ℂ)), MvPolynomial.eval z p = 0) ↔ _
  constructor
  · intro hz p; exact hz p.val p.property
  · intro hz p hp; exact hz ⟨p,hp⟩

theorem SemialgebraicOn.affine {ι κ : Type*} [Fintype ι] [Finite κ]
    {B : Set (ι → ℝ)} (hB : PolynomialSignSet id B)
    (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (b : κ → ℝ) :
    SemialgebraicOn B (fun y => L y + b) := by
  classical
  let p (j : κ) : MvPolynomial ι ℝ :=
    (∑ i, MvPolynomial.C (L (Pi.single i 1) j) * MvPolynomial.X i) + MvPolynomial.C (b j)
  apply (SemialgebraicOn.polynomial hB p).congr
  intro y _
  have hy : y = ∑ i : ι, y i • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  funext j
  simp only [p,MvPolynomial.eval_add,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,Pi.add_apply]
  congr 1
  conv_rhs => rw [hy]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma polynomialSignSet_real_ball {ι : Type*} [Fintype ι] (p : ι → ℝ) (r : ℝ) :
    PolynomialSignSet id {y : ι → ℝ | ‖y-p‖ < r} := by
  convert PolynomialSignSet.norm_lt_polynomial (c := id)
    (fun j => MvPolynomial.X j - MvPolynomial.C (p j)) (MvPolynomial.C r) using 1
  ext y
  simp only [mem_ofPred_eq,id_eq,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,Pi.sub_def]

theorem semialgebraicOn_inverse_restrict {ι κ : Type*}
    {B : Set (ι → ℝ)} {T : Set (κ → ℝ)}
    (hB : PolynomialSignSet id B) (g : (κ → ℝ) → (ι → ℝ))
    (hg : SemialgebraicOn T g) (f : (ι → ℝ) → (κ → ℝ))
    (hf : MapsTo f B T) (hgf : ∀ x ∈ B, g (f x) = x)
    (hfg : ∀ y ∈ T, g y ∈ B → f (g y) = y) : SemialgebraicOn B f := by
  have hh := hg.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => (z.2,z.1))
    (Equiv.sumComm κ ι) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  have hb := hB.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intros; rfl)
  unfold SemialgebraicOn
  convert hb.inter hh using 1
  ext ⟨x,y⟩
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,rfl⟩
    exact ⟨hx,hf hx,(hgf _ hx).symm⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,(hfg _ hy (he ▸ hx)).symm.trans (congrArg f he.symm)⟩

theorem affine_inverse_germ_semialgebraic {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Set (κ → ℝ)} (hV : PolynomialSignSet id V)
    (f : (ι → ℝ) → (κ → ℝ)) (L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (b : ι → ℝ)
    (hf : ContinuousAt f 0)
    (hgf : ∀ᶠ x in 𝓝 (0 : ι → ℝ), L (f x) + b = x)
    (hfg : ∀ᶠ y in 𝓝[V] (f 0), f (L y + b) = y)
    (hfv : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ V) :
    ∃ r : ℝ, 0 < r ∧ SemialgebraicOn {x : ι → ℝ | ‖x‖ < r} f := by
  have hfg' := eventually_nhdsWithin_iff.mp hfg
  obtain ⟨ρ,hρ,hρfg⟩ := Metric.mem_nhds_iff.mp hfg'
  let T := V ∩ {y : κ → ℝ | ‖y-f 0‖ < ρ}
  have hT : PolynomialSignSet id T := hV.inter (polynomialSignSet_real_ball (f 0) ρ)
  have hnear : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ T := by
    have hh : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ Metric.ball (f 0) ρ :=
      hf.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
    filter_upwards [hfv,hh] with x hx hx'
    exact ⟨hx,by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hx'⟩
  obtain ⟨r,hr,hrinv⟩ := Metric.mem_nhds_iff.mp (hnear.and hgf)
  refine ⟨r,hr,?_⟩
  apply semialgebraicOn_inverse_restrict
    (by simpa only [sub_zero] using polynomialSignSet_real_ball (0 : ι → ℝ) r)
    (fun y => L y+b) (SemialgebraicOn.affine hT L b) f
  · intro x hx
    exact (hrinv (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hx)).1
  · intro x hx
    exact (hrinv (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hx)).2
  · intro y hy _
    exact hρfg (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hy.2) hy.1
end Release061

end

end OAI
