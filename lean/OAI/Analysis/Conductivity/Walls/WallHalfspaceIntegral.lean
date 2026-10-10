import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection
import OAI.Analysis.Conductivity.Walls.WallHomogeneous

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma hasCompactSupport_prodMkLeft {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space E] {f : E×F → ℝ} (hf : HasCompactSupport f) (x : E) :
    HasCompactSupport (fun y => f (x,y)) := by
  apply hf.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight x, ?_⟩
  convert (isClosed_singleton (x := x)).prod (isClosed_univ : IsClosed (Set.univ : Set F)) using 1
  ext p
  rcases p with ⟨p₁,p₂⟩
  simp [Prod.ext_iff,eq_comm]

lemma hasCompactSupport_prodMkRight {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {f : E×F → ℝ} (hf : HasCompactSupport f) (y : F) :
    HasCompactSupport (fun x => f (x,y)) := by
  apply hf.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft y, ?_⟩
  convert (isClosed_univ : IsClosed (Set.univ : Set E)).prod (isClosed_singleton (x := y)) using 1
  ext p
  rcases p with ⟨p₁,p₂⟩
  simp [Prod.ext_iff,eq_comm]

lemma wallDerivative_slice {g : Box3 → ℝ} (hg : Differentiable ℝ g) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative g (q,z)=deriv (fun t => g (q,t)) z := by
  have hh : HasDerivAt (fun t => (q,t)) (0,1) z :=
    (hasDerivAt_const z q).prodMk (hasDerivAt_id z)
  exact ((hg (q,z)).hasFDerivAt.comp_hasDerivAt z hh).deriv.symm

lemma wallAlong_slice {f : Box3 → ℝ} (hf : Differentiable ℝ f) (d q : ℝ×ℝ) (z : ℝ) :
    wallAlong d f (q,z)=fderiv ℝ (fun p => f (p,z)) q d := by
  have hh : HasFDerivAt (fun p : ℝ×ℝ => (p,z))
      ((ContinuousLinearMap.id ℝ (ℝ×ℝ)).prod (0 : (ℝ×ℝ) →L[ℝ] ℝ)) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const z q)
  change wallAlong d f (q,z)=fderiv ℝ (f∘(fun p => (p,z))) q d
  rw [((hf (q,z)).hasFDerivAt.comp q hh).fderiv]
  rfl

lemma wallAlong_integral_slice {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hs : HasCompactSupport f) (d : ℝ×ℝ) (z : ℝ) :
    (∫ q,wallAlong d f (q,z))=0 := by
  let g := fun q : ℝ×ℝ => f (q,z)
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.comp (contDiff_id.prodMk contDiff_const)
  have hgs : HasCompactSupport g := hasCompactSupport_prodMkRight hs z
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (ℝ×ℝ))) (f := fun _ : ℝ×ℝ => (1:ℝ)) (g := g) (v := d)
    (by simp)
    (by simpa using ((hg.fderiv_right (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const).continuous.integrable_of_hasCompactSupport (hgs.fderiv_apply ℝ d))
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgs)
    (fun p _ => differentiableAt_const 1) (fun p _ => hg.differentiable (by simp) p)
  simpa [wallAlong_slice (hf.differentiable (by simp)),g] using hi

theorem wall_halfspace_flux {f g : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (d : ℝ×ℝ) :
    (∫ p in (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ),
      wallAlong d f p+wallDerivative g p)= -(∫ q : ℝ×ℝ,g (q,0)) := by
  have hif : Integrable (wallAlong d f) :=
    (wallAlong_smooth d hf).continuous.integrable_of_hasCompactSupport (hsf.fderiv_apply ℝ (d,0))
  have hig : Integrable (wallDerivative g) :=
    (wallDerivative_smooth hg).continuous.integrable_of_hasCompactSupport (hsg.fderiv_apply ℝ (0,1))
  have hm : (volume : Measure Box3).restrict ((Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ))=
      (volume : Measure (ℝ×ℝ)).prod ((volume : Measure ℝ).restrict (Ioi 0)) := by
    change ((volume : Measure (ℝ×ℝ)).prod (volume : Measure ℝ)).restrict _=_
    rw [←Measure.prod_restrict,Measure.restrict_univ]
  rw [integral_add hif.integrableOn hig.integrableOn]
  have hfzero : (∫ p in (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ),wallAlong d f p)=0 := by
    rw [hm,integral_prod_symm]
    · simp_rw [wallAlong_integral_slice hf hsf d,integral_zero]
    · rw [←hm]; exact hif.integrableOn
  rw [hfzero,zero_add,hm,integral_prod]
  · simp_rw [wallDerivative_slice (hg.differentiable (by simp))]
    have he (q : ℝ×ℝ) : (∫ z in Ioi (0:ℝ),deriv (fun t => g (q,t)) z)= -g (q,0) :=
      HasCompactSupport.integral_Ioi_deriv_eq
        ((hg.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id))
        (hasCompactSupport_prodMkLeft hsg q) 0
    simp_rw [he,integral_neg]
  · rw [←hm]; exact hig.integrableOn

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma wallAlong_sCoordinate (p : Box3) : wallAlong (1,0) (fun q : Box3 => q.1.1) p=1 := by
  exact cubePartial_fst_fst ((1,0),0) p

lemma wallDerivative_sCoordinate (p : Box3) : wallDerivative (fun q : Box3 => q.1.1) p=0 := by
  exact cubePartial_fst_fst ((0,0),1) p

lemma wallAlong_sub_box {f g : Box3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (d : ℝ×ℝ) (p : Box3) :
    wallAlong d (fun q => f q-g q) p=wallAlong d f p-wallAlong d g p := by
  simp only [wallAlong,fderiv_fun_sub (hf p) (hg p),sub_apply]

lemma wallAlong_neg (f : Box3 → ℝ) (d : ℝ×ℝ) (p : Box3) :
    wallAlong d (fun q => -f q) p= -wallAlong d f p := by
  simp only [wallAlong,fderiv_fun_neg,neg_apply]

lemma wall_torque_divergence {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (p : Box3) :
    v p*wallDerivative A p-p.1.1*(wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p)=
    wallAlong (1,0) (fun q => -q.1.1*(A q*wallDerivative v q)) p+
      wallDerivative (fun q => v q*A q-q.1.1*(A q*wallAlong (1,0) v q+B q*wallDerivative v q)) p := by
  let F := fun q => A q*wallDerivative v q
  let G := fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q
  have hF := (hA.mul (wallDerivative_smooth hv)).differentiable (by simp)
  have hG := ((hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))).differentiable (by simp)
  have hs : Differentiable ℝ (fun q : Box3 => q.1.1) := differentiable_fst.comp differentiable_fst
  have hAd := hA.differentiable (by simp)
  have hvd := hv.differentiable (by simp)
  change v p*wallDerivative A p-p.1.1*(wallAlong (1,0) F p+wallDerivative G p)=
    wallAlong (1,0) (fun q => -q.1.1*F q) p+
      wallDerivative (fun q => v q*A q-q.1.1*G q) p
  rw [wallAlong_mul (f := fun q : Box3 => -q.1.1) (g := F) (1,0) hs.neg hF,wallAlong_neg,wallAlong_sCoordinate,
    wallDerivative_sub (f := fun q => v q*A q) (g := fun q => q.1.1*G q) (hvd.mul hAd) (hs.mul hG),wallDerivative_mul hvd hAd,
    wallDerivative_mul (f := fun q : Box3 => q.1.1) (g := G) hs hG,wallDerivative_sCoordinate]
  dsimp [F]
  ring

theorem wall_matrix_halfspace_moments {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hsA : HasCompactSupport A) (hsB : HasCompactSupport B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hz : ∀ q,wallDerivative v (q,0)=0) :
    let U := (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ)
    let r₁ := wallDerivative A
    let r₂ := fun p => wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p
    (∫ p in U,r₁ p)= -(∫ q : ℝ×ℝ,A (q,0)) ∧
    (∫ p in U,r₂ p)= -(∫ q : ℝ×ℝ,A (q,0)*wallAlong (1,0) v (q,0)) ∧
    (∫ p in U,v p*r₁ p-p.1.1*r₂ p)=
      -(∫ q : ℝ×ℝ,A (q,0)*(v (q,0)-q.1*wallAlong (1,0) v (q,0))) := by
  dsimp only
  have hF := hA.mul (wallDerivative_smooth hv)
  have hG := (hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))
  have hsF : HasCompactSupport (fun q => A q*wallDerivative v q) := hsA.mul_right
  have hsG : HasCompactSupport (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) :=
    hsA.mul_right.add hsB.mul_right
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : Box3 => q.1.1) := contDiff_fst.comp contDiff_fst
  refine ⟨?_,?_,?_⟩
  · have hh := wall_halfspace_flux (f := fun _ : Box3 => 0) contDiff_const hA HasCompactSupport.zero hsA (1,0)
    simpa [wallAlong] using hh
  · have hh := wall_halfspace_flux hF hG hsF hsG (1,0)
    simpa only [hz,mul_zero,add_zero] using hh
  · have hh := wall_halfspace_flux
      (hs.neg.mul hF) ((hv.mul hA).sub (hs.mul hG))
      hsF.mul_left (hsA.mul_left.sub hsG.mul_left) (1,0)
    simp_rw [←wall_torque_divergence hA hB hv] at hh
    convert hh using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with q
    simp only [hz,mul_zero,add_zero]
    ring

end ScalarConductivity

end

end OAI
