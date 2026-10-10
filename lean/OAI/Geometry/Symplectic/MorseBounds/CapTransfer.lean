import OAI.Geometry.Symplectic.MorseBounds.Periodization
import OAI.Geometry.Symplectic.MorseBounds.CapEnd

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapTransfer
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.CapProduct
open MorseArnold.ProductLocal MorseArnold.AmbientHamiltonian
open scoped Manifold ContDiff Topology
noncomputable section
abbrev AE := Model 4 × ((Model 2 × Model 2) × (Model 2 × Model 2))
abbrev AJ := 𝓘(ℝ,AE)
instance ambientCharts {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X] :
    ChartedSpace AE (X × SphereFour) :=
  prodChartedSpace (Model 4) X
    (ModelProd (ModelProd (Model 2) (Model 2)) (ModelProd (Model 2) (Model 2))) SphereFour
def CapTransferObligation : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] [T2Space X] [SecondCountableTopology X]
    [CompactSpace X] [ConnectedSpace X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X)) (F : X × PlaneFour → ℝ),
    GenericGeometry.IsMorse (E := LE) F →
    (∀ p, 9 ≤ totalSq p.2 → F p = ProductLocal.quadratic p.2) →
    ∀ l : ℝ, 25/2 < l →
    ∃ (w : SymplecticProduct.SymplecticForm AI (M := X × SphereFour))
      (H : ℝ × (X × SphereFour) → ℝ) (Phi : ℝ × (X × SphereFour) → X × SphereFour)
      (V : ℝ → (x : X × SphereFour) → TangentSpace AI x),
      (∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
        ((areaValue l p.2.1.1 u.2.1.1 v.2.1.1 + areaValue l p.2.1.2 u.2.1.2 v.2.1.2) +
         (areaValue l p.2.2.1 u.2.2.1 v.2.2.1 + areaValue l p.2.2.2 u.2.2.2 v.2.2.2))) ∧
      ContMDiff (𝓘(ℝ).prod AI) 𝓘(ℝ) ∞ H ∧
      (∀ t x, H (t+1,x) = H (t,x)) ∧
      ContMDiff (𝓘(ℝ).prod AI) AI ∞ Phi ∧
      (∀ x, Phi (0,x) = x) ∧
      (∀ t x, w.form x (V t x) = mvfderiv AI (fun y => H (t,y)) x) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ) AI (fun s => Phi (s,x)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (Phi (t,x))))) ∧
      {x | Phi (1,x) = x}.Finite ∧
      Nat.card {x // Phi (1,x) = x} = 16 * Nat.card {x // x ∈ GenericGeometry.criticalSet (E := LE) F} ∧
      (∀ x, Phi (1,x) = x → Conjugacy.NondegenerateAt AI (fun y => Phi (1,y)) x)
end
end MorseArnold.CapTransfer

namespace MorseArnold.CapTransfer
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.CapProduct
open MorseArnold.ProductLocal MorseArnold.AmbientHamiltonian
open MorseArnold.LocalCorrection MorseArnold.HamiltonianComposition
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
lemma ambient_model : AI = AJ := by
  simp only [AI,AJ,AE,SP, modelWithCornersSelf_prod.symm]
lemma local_model : (𝓡 4).prod PP = LI := by
  simp only [PP,LI,ProductLocal.LE,Model, modelWithCornersSelf_prod.symm]

lemma preserves_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (w : TwoForm (E := E) (M := M)) (a b : M → M)
    (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a) (hb : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ b)
    (hwa : PreservesForm w a) (hwb : PreservesForm w b) :
    PreservesForm w (a ∘ b) := by
  intro x u v
  rw [mfderiv_comp x (ha.mdifferentiable (by simp) (b x)) (hb.mdifferentiable (by simp) x)]
  exact (hwa (b x) _ _).trans (hwb x u v)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]

omit [IsManifold (𝓡 4) ∞ X] in
lemma local_charts :
    prodChartedSpace (Model 4) X (ModelProd (ModelProd Plane Plane) (ModelProd Plane Plane)) PlaneFour =
    (ProductLocal.productCharts : ChartedSpace ProductLocal.LE (X × PlaneFour)) := by
  ext1
  · simp [atlas,ChartedSpace.atlas,OpenPartialHomeomorph.refl_prod_refl]
  · funext x
    ext1 <;> simp [chartAt,ChartedSpace.chartAt,OpenPartialHomeomorph.refl_prod_refl]

omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma exterior_zero (x : X × PlaneFour) : exteriorFlow 0 x = x :=
  Prod.ext rfl (quadFlow_zero x.2)
omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma exterior_inverse_neg (t : ℝ) (x : X × PlaneFour) :
    exteriorFlow (-t) (exteriorFlow t x) = x := by
  simpa only [neg_neg] using exterior_inverse (-t) x

def deltaInv (eps : ℝ) (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (p : ℝ × (X × PlaneFour)) : X × PlaneFour :=
  exteriorFlow (eps*p.1) (phi (-eps*p.1,p.2))

lemma delta_inverse_data (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (F : X × PlaneFour → ℝ) (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour) (eps : ℝ)
    (hm : LocalModel wX F w phi eps) :
    ContMDiff (𝓘(ℝ).prod LI) LI ∞ (deltaInv eps phi) ∧
    (∀ t x, 9 ≤ totalSq x.2 → deltaInv eps phi (t,x) = x) ∧
    (∀ t x, x.2 ∈ box → (deltaInv eps phi (t,x)).2 ∈ box) ∧
    (∀ t x, deltaInv eps phi (t,delta eps phi (t,x)) = x) ∧
    (∀ t x, delta eps phi (t,deltaInv eps phi (t,x)) = x) := by
  obtain ⟨hw,hphi,hzero,hadd,hODE,hext,hbox,rest⟩ := hm
  refine ⟨exterior_smooth.comp ((contMDiff_const.mul contMDiff_fst).prodMk
    (rescale_smooth phi hphi (-eps))), ?_, ?_, ?_, ?_⟩
  · intro t x hx
    change exteriorFlow (eps*t) (phi (-eps*t,x)) = x
    rw [hext _ _ hx]
    simpa only [neg_mul] using exterior_inverse (eps*t) x
  · intro t x hx
    exact quadFlow_box _ _ (hbox _ _ hx)
  · intro t x
    change exteriorFlow (eps*t) (phi (-eps*t,phi (eps*t,exteriorFlow (-eps*t) x))) = x
    rw [← hadd,show -eps*t+eps*t=0 by ring,hzero]
    simpa only [neg_mul] using exterior_inverse (eps*t) x
  · intro t x
    change phi (eps*t,exteriorFlow (-eps*t) (exteriorFlow (eps*t) (phi (-eps*t,x)))) = x
    rw [show -eps*t = -(eps*t) by ring,exterior_inverse_neg,← hadd,
      add_neg_cancel,hzero]

lemma delta_preserves (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (F : X × PlaneFour → ℝ) (hF : GenericGeometry.IsMorse (E := LE) F)
    (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour) (eps : ℝ)
    (hm : LocalModel wX F w phi eps) (t : ℝ) :
    PreservesForm w.form (fun x => delta eps phi (t,x)) := by
  obtain ⟨hw,hphi,hzero,hadd,hODE,hext,hbox,rest⟩ := hm
  have hQf : GenericGeometry.hamiltonianField w (fun q : X × PlaneFour => ProductLocal.quadratic q.2) =
      (fun q => (0,quadVelocity q.2)) := by
    funext q
    apply w.nondegenerate q
    rw [GenericGeometry.hamiltonianField_equation,quadratic_hamiltonian wX w hw]
  have hQs := GenericGeometry.hamiltonianField_smooth w (fun q : X × PlaneFour => ProductLocal.quadratic q.2) quadratic_msmooth
  rw [hQf] at hQs
  have hps : PreservesForm w.form (fun x => phi (eps*t,x)) := by
    intro x u v
    exact GenericGeometry.manifold_hamiltonian_flow_preserves_form w F hF.1 _
      (GenericGeometry.hamiltonianField_smooth w F hF.1)
      (GenericGeometry.hamiltonianField_equation w F) phi hphi hzero hODE (eps*t) x u v
  have hqs : PreservesForm w.form (exteriorFlow (-eps*t)) := by
    intro x u v
    exact GenericGeometry.manifold_hamiltonian_flow_preserves_form w _ quadratic_msmooth _ hQs
      (quadratic_hamiltonian wX w hw) _ exterior_smooth exterior_zero quadratic_integral (-eps*t) x u v
  exact preserves_comp w.form _ _ (hphi.comp (contMDiff_const.prodMk contMDiff_id))
    (exterior_smooth.comp (contMDiff_const.prodMk contMDiff_id)) hps hqs
end
end MorseArnold.CapTransfer

namespace MorseArnold.CapTransfer
open MorseArnold.HamiltonianComposition MorseArnold.CapGluing
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
variable {ι M N E F : Type*} [Finite ι] [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ChartedSpace E M] [ChartedSpace F N] [IsManifold 𝓘(ℝ,E) ∞ M]
  [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space M]
local notation "I" => 𝓘(ℝ,E)
local notation "J" => 𝓘(ℝ,F)
omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
lemma insert_preserves
    (wM : TwoForm (E := E) (M := M)) (wN : TwoForm (E := F) (M := N))
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (hw : ∀ i x, x ∈ (e i).source → ∀ u v,
      wN (e i x) (mfderiv I J (e i) x u) (mfderiv I J (e i) x v) = wM x u v)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (d : ℝ × N → N) (hd : ContMDiff (𝓘(ℝ).prod J) J ∞ d)
    (hid : ∀ t y, y ∉ C → d (t,y) = y)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target)
    (hS : ∀ t, PreservesForm wN (fun y => d (t,y))) (t : ℝ) :
    PreservesForm wM (fun x => insert e d (t,x)) := by
  let g : M → M := fun x => insert e d (t,x)
  have hg : ContMDiff I I ∞ g :=
    (insert_smooth e hdis he hei C hC hsub d hd hid hmap).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hs : ContMDiff J J ∞ (fun x => d (t,x)) :=
    hd.comp (contMDiff_const.prodMk contMDiff_id)
  intro x u v
  change wM (g x) (mfderiv I I g x u) (mfderiv I I g x v) = wM x u v
  by_cases hx : ∃ i, x ∈ (e i).source
  · obtain ⟨i,hi⟩ := hx
    have hm := hmap t i ((e i).map_source hi)
    have hgx : g x = (e i).symm (d (t,e i x)) := insert_in_source e hdis d t i x hi
    have hgxmem : g x ∈ (e i).source := hgx ▸ (e i).map_target hm
    have hloc : (e i) ∘ g =ᶠ[𝓝 x] (fun y => d (t,e i y)) := by
      filter_upwards [(e i).open_source.mem_nhds hi] with y hy
      dsimp only [Function.comp_apply,g]
      rw [insert_in_source e hdis d t i y hy]
      exact (e i).right_inv (hmap t i ((e i).map_source hy))
    have hdx := ((he i x hi).contMDiffAt ((e i).open_source.mem_nhds hi)).mdifferentiableAt (by simp)
    have hdy := ((he i (g x) hgxmem).contMDiffAt ((e i).open_source.mem_nhds hgxmem)).mdifferentiableAt (by simp)
    have hD : (mfderiv I J (e i) (g x)).comp (mfderiv I I g x) =
        (mfderiv J J (fun y => d (t,y)) (e i x)).comp (mfderiv I J (e i) x) := by
      rw [← mfderiv_comp x hdy (hg.mdifferentiable (by simp) x)]
      rw [hloc.mfderiv_eq]
      exact mfderiv_comp x (hs.mdifferentiable (by simp) (e i x)) hdx
    have hDu := congrArg (fun L : E →L[ℝ] F => L u) hD
    have hDv := congrArg (fun L : E →L[ℝ] F => L v) hD
    have hpoint : e i (g x) = d (t,e i x) := hloc.eq_of_nhds
    have hform := hw i (g x) hgxmem (mfderiv I I g x u) (mfderiv I I g x v)
    change mfderiv I J (e i) (g x) (mfderiv I I g x u) =
      mfderiv J J (fun y => d (t,y)) (e i x) (mfderiv I J (e i) x u) at hDu
    change mfderiv I J (e i) (g x) (mfderiv I I g x v) =
      mfderiv J J (fun y => d (t,y)) (e i x) (mfderiv I J (e i) x v) at hDv
    erw [hpoint,hDu,hDv] at hform
    exact hform.symm.trans ((hS t (e i x) _ _).trans (hw i x hi u v))
  · let S : Set M := ⋃ i, (e i).symm '' C
    have hcomp : IsCompact S := isCompact_iUnion fun i =>
      hC.image_of_continuousOn ((e i).continuousOn_symm.mono (hsub i))
    have hnot : x ∉ S := by
      rintro ⟨_,⟨i,rfl⟩,y,hy,heq⟩
      exact hx ⟨i,heq ▸ (e i).map_target (hsub i hy)⟩
    have hloc : g =ᶠ[𝓝 x] id := by
      filter_upwards [hcomp.isClosed.isOpen_compl.mem_nhds hnot] with y hy
      apply insert_off_support e hdis C d hid t y
      intro i hi
      exact hy (Set.mem_iUnion.mpr ⟨i,hi⟩)
    have hpoint : g x = x := hloc.eq_of_nhds
    have hD : mfderiv I I g x = ContinuousLinearMap.id ℝ E := by
      rw [hloc.mfderiv_eq,mfderiv_id]; rfl
    simp only [TangentSpace] at hD ⊢
    rw [hD]
    exact congrArg (fun y => wM y u v) hpoint
end
end MorseArnold.CapTransfer

namespace MorseArnold.CapTransfer
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.CapProduct
open MorseArnold.ProductLocal MorseArnold.AmbientHamiltonian
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
local instance capTransferFinrankR3 : Fact (Module.finrank ℝ R3 = 2+1) := ⟨by simp [R3]⟩
variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]
lemma cap_form (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (wL : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (hL : ∀ p u v, wL.form p u v = wX.form p.1 u.1 v.1 +
      CapSymplectic.planeArea u.2.1.1 v.2.1.1 + CapSymplectic.planeArea u.2.1.2 v.2.1.2 +
      CapSymplectic.planeArea u.2.2.1 v.2.2.1 + CapSymplectic.planeArea u.2.2.2 v.2.2.2)
    (l : ℝ) (hl : 25/2 < l)
    (wM : SymplecticProduct.SymplecticForm AI (M := X × SphereFour))
    (hM : ∀ p u v, wM.form p u v = wX.form p.1 u.1 v.1 +
        ((areaValue l p.2.1.1 u.2.1.1 v.2.1.1 + areaValue l p.2.1.2 u.2.1.2 v.2.1.2) +
         (areaValue l p.2.2.1 u.2.2.1 v.2.2.1 + areaValue l p.2.2.2 u.2.2.2 v.2.2.2)))
    (i : Choices) (x : X × SphereFour) (hx : x ∈ (CapEnd.chart (X := X) l (by linarith) i).source)
    (u v : TangentSpace AJ x) :
    wL.form (CapEnd.chart l (by linarith) i x)
      (mfderiv AJ LI (CapEnd.chart (X := X) l (by linarith) i) x u)
      (mfderiv AJ LI (CapEnd.chart (X := X) l (by linarith) i) x v) = wM.form x u v := by
  obtain ⟨ws,hws⟩ := SphereSymplectic.scaled_standardSphere_symplectic l (by linarith)
  have hc := CapSymplectic.allChart_area wX l hl i ws hws x hx u v
  simp only [CapSymplectic.fourPlaneForm,CapSymplectic.fourSphereForm,
    SymplecticProduct.prodForm_apply] at hc
  change wX.form (CapEnd.chart l (by linarith) i x).1
      (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x u).1
      (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v).1 +
      ((CapSymplectic.planeArea (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x u).2.1.1
          (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v).2.1.1 +
        CapSymplectic.planeArea (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x u).2.1.2
          (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v).2.1.2) +
       (CapSymplectic.planeArea (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x u).2.2.1
          (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v).2.2.1 +
        CapSymplectic.planeArea (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x u).2.2.2
          (mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v).2.2.2)) =
      wX.form x.1 u.1 v.1 + ((ws.form x.2.1.1 u.2.1.1 v.2.1.1 + ws.form x.2.1.2 u.2.1.2 v.2.1.2) +
        (ws.form x.2.2.1 u.2.2.1 v.2.2.1 + ws.form x.2.2.2 u.2.2.2 v.2.2.2)) at hc
  have hd (v : AE) : mfderiv AI ((𝓡 4).prod PP) (CapEnd.chart (X := X) l (by linarith) i) x v =
      mfderiv AJ LI (CapEnd.chart (X := X) l (by linarith) i) x v := by
    have h₁ := congrArg (fun I : ModelWithCorners ℝ AE AE =>
      (show ProductLocal.LE from mfderiv I ((𝓡 4).prod PP)
        (CapEnd.chart (X := X) l (by linarith) i) x v)) ambient_model
    have h₂ : (show ProductLocal.LE from mfderiv AJ ((𝓡 4).prod PP)
        (CapEnd.chart (X := X) l (by linarith) i) x v) =
        mfderiv AJ LI (CapEnd.chart (X := X) l (by linarith) i) x v := by
      rw [local_charts]
      exact congrArg (fun J : ModelWithCorners ℝ ProductLocal.LE ProductLocal.LE =>
        (show ProductLocal.LE from mfderiv AJ J
          (CapEnd.chart (X := X) l (by linarith) i) x v)) local_model
    exact h₁.trans h₂
  rw [hd u,hd v] at hc
  have ha := congrArg (fun z : ℝ => wX.form x.1 u.1 v.1 + z)
    (congrArg₂ (fun a b : ℝ => a+b)
      (congrArg₂ (fun a b : ℝ => a+b)
        (hws x.2.1.1 u.2.1.1 v.2.1.1) (hws x.2.1.2 u.2.1.2 v.2.1.2))
      (congrArg₂ (fun a b : ℝ => a+b)
        (hws x.2.2.1 u.2.2.1 v.2.2.1) (hws x.2.2.2 u.2.2.2 v.2.2.2)))
  erw [hL,hM]
  simpa only [areaValue,SphereSymplectic.tangentInclusion,add_assoc] using! hc.trans ha
end
end MorseArnold.CapTransfer

namespace MorseArnold.CapTransfer
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.CapProduct
open MorseArnold.ProductLocal MorseArnold.AmbientHamiltonian
open MorseArnold.LocalCorrection MorseArnold.HamiltonianComposition
open MorseArnold.CapGluing
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
local instance capTransferObligationFinrankR3 : Fact (Module.finrank ℝ R3 = 2+1) := ⟨by simp [R3]⟩
 theorem capTransferObligation : CapTransferObligation := by
  intro X _ _ _ _ _ _ _ wX F hF hFq l hl
  let : IsManifold AJ ∞ (X × SphereFour) := by
    rw [← ambient_model]
    exact IsManifold.prod (I := 𝓡 4) (I' := SP) (M := X) (M' := SphereFour)
  obtain ⟨wL,phi,eps,hm,hd,hK,hsupp,hmap,V,hV,hODE⟩ := correctionObligation X wX F hF hFq
  have hm' := hm
  obtain ⟨hwL,hphi,hzero,hadd,hphiODE,hext,hbox,hfinite,hcrit,heps,hepspi,hfix,hnd⟩ := hm'
  obtain ⟨wM,hwM,hB,hVB,hb,hbz,hbadd,hbODE,hbfix,hbout,hbend⟩ :=
    ambientHamiltonianObligation wX l eps hl heps hepspi
  have hbj : ContMDiff (𝓘(ℝ).prod AJ) AJ ∞
      (fun q : ℝ × (X × SphereFour) => ambientFlow l eps q.1 q.2) := by
    simpa only [ambient_model] using hb
  have hBj : ContMDiff AJ 𝓘(ℝ) ∞ (ambientPotential (X := X) l eps) := by
    simpa only [ambient_model] using hB
  have hVBj : ∀ x, wM.form x (ambientVelocity l eps x) = mvfderiv AJ (ambientPotential l eps) x := by
    intro x
    ext u
    have heq : mfderiv AI 𝓘(ℝ) (ambientPotential l eps) x u =
        mfderiv AJ 𝓘(ℝ) (ambientPotential l eps) x u :=
      congrArg (fun I : ModelWithCorners ℝ AE AE =>
        (show ℝ from mfderiv I 𝓘(ℝ) (ambientPotential l eps) x u)) ambient_model
    exact (congrArg (fun L : AE →L[ℝ] ℝ => L u) (hVB x)).trans heq
  have hbODEj : ∀ (t : ℝ) (x : X × SphereFour), HasMFDerivAt 𝓘(ℝ) AJ (fun r => ambientFlow l eps r x) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (ambientVelocity l eps (ambientFlow l eps t x))) := by
    intro t x
    have heq := congrArg (fun model : ModelWithCorners ℝ AE AE =>
      HasMFDerivAt 𝓘(ℝ) model (fun r => ambientFlow l eps r x) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (show TangentSpace model (ambientFlow l eps t x) from
            ambientVelocity l eps (ambientFlow l eps t x)))) ambient_model
    exact heq.mp (hbODE t x)
  let e := CapEnd.chart (X := X) l (by linarith)
  have hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source) := CapEnd.chart_disjoint l hl
  have htarg (i : Choices) : (e i).target = univ ×ˢ box := CapEnd.chart_target l hl i
  have he (i : Choices) : ContMDiffOn AJ LI ∞ (e i) (e i).source := by
    have h := (CapEnd.chart_smooth (𝓡 4) l hl i (X := X)).1
    change ContMDiffOn AI ((𝓡 4).prod PP) ∞ (e i) (e i).source at h
    rw [local_charts] at h
    simpa only [ambient_model,local_model] using h
  have hei (i : Choices) : ContMDiffOn LI AJ ∞ (e i).symm (e i).target := by
    have h := (CapEnd.chart_smooth (𝓡 4) l hl i (X := X)).2
    change ContMDiffOn ((𝓡 4).prod PP) AI ∞ (e i).symm (e i).target at h
    rw [local_charts] at h
    simpa only [ambient_model,local_model] using h
  let C : Set (X × PlaneFour) := {x | totalSq x.2 ≤ 9}
  have hC : IsCompact C := core_compact
  have hsub (i : Choices) : C ⊆ (e i).target := by
    intro x hx
    rw [htarg]
    exact ⟨mem_univ _,in_box_of_totalSq x.2 hx⟩
  have hid : ∀ t x, x ∉ C → delta eps phi (t,x) = x := by
    intro t x hx; exact (hsupp t x (le_of_lt (lt_of_not_ge hx))).1
  have hKzero : ∀ t x, x ∉ C → K F eps phi (t,x) = 0 := by
    intro t x hx; exact (hsupp t x (le_of_lt (lt_of_not_ge hx))).2
  have hmapd : ∀ t i, MapsTo (fun x => delta eps phi (t,x)) (e i).target (e i).target := by
    intro t i x hx; rw [htarg] at hx ⊢; exact ⟨mem_univ _,hmap t x hx.2⟩
  have hform (i : Choices) (x : X × SphereFour) (hx : x ∈ (e i).source) (u v : TangentSpace AJ x) :
      wL.form (e i x) (mfderiv AJ LI (e i) x u) (mfderiv AJ LI (e i) x v) = wM.form x u v :=
    cap_form wX wL hwL l hl wM hwM i x hx u v
  obtain ⟨W,has,hAs,hWA,hODEa⟩ := CapHamiltonian.insert_hamiltonian wM.form wL.form e hdis
    he hei hform C hC hsub (delta eps phi) (K F eps phi) V hd hK hid hKzero hmapd hV hODE
  obtain ⟨hdInv,hInvsupp,hInvbox,hInv,hInv'⟩ := delta_inverse_data wX F wL phi eps hm
  have hidi : ∀ t x, x ∉ C → deltaInv eps phi (t,x) = x := by
    intro t x hx; exact hInvsupp t x (le_of_lt (lt_of_not_ge hx))
  have hmapi : ∀ t i, MapsTo (fun x => deltaInv eps phi (t,x)) (e i).target (e i).target := by
    intro t i x hx; rw [htarg] at hx ⊢; exact ⟨mem_univ _,hInvbox t x hx.2⟩
  let a := insert e (delta eps phi)
  let ai := insert e (deltaInv eps phi)
  let b : ℝ × (X × SphereFour) → X × SphereFour := fun q => ambientFlow l eps q.1 q.2
  let A := generator e (K F eps phi)
  let B : ℝ × (X × SphereFour) → ℝ := fun q => ambientPotential l eps q.2
  have hais : ContMDiff (𝓘(ℝ).prod AJ) AJ ∞ ai :=
    insert_smooth e hdis he hei C hC hsub (deltaInv eps phi) hdInv hidi hmapi
  have har : ∀ t, Function.RightInverse (fun x => ai (t,x)) (fun x => a (t,x)) :=
    insert_inverse e hdis (deltaInv eps phi) (delta eps phi) hmapi hInv'
  have hal : ∀ t, Function.LeftInverse (fun x => ai (t,x)) (fun x => a (t,x)) :=
    insert_inverse e hdis (delta eps phi) (deltaInv eps phi) hmapd hInv
  have hsp : ∀ t, PreservesForm wM.form (fun x => a (t,x)) :=
    insert_preserves wM.form wL.form e hdis he hei hform C hC hsub (delta eps phi)
      hd hid hmapd (delta_preserves wX F hF wL phi eps hm)
  have hc := hamiltonian_path_composition wM.form a ai b has hais hbj har hal hsp A B hAs
    (hBj.comp contMDiff_snd) W (fun _ x => ambientVelocity l eps x) hWA
    (fun _ x => hVBj x) hODEa hbODEj
  dsimp only at hc
  let L : ℝ × (X × SphereFour) → ℝ := fun q => A q + B (q.1,ai q)
  let g : ℝ × (X × SphereFour) → X × SphereFour := fun q => a (q.1,b q)
  let Z : ℝ → (x : X × SphereFour) → TangentSpace AJ x := fun t x =>
    (show AE from W t x) +
      (show AE from mfderiv AJ AJ (fun y => a (t,y)) (ai (t,x)) (ambientVelocity l eps (ai (t,x))))
  have hL : ContMDiff (𝓘(ℝ).prod AJ) 𝓘(ℝ) ∞ L := hc.1
  have hg : ContMDiff (𝓘(ℝ).prod AJ) AJ ∞ g := hc.2.1
  have hZ : ∀ t x, wM.form x (Z t x) = mvfderiv AJ (fun y => L (t,y)) x := hc.2.2.1
  have hgODE : ∀ t x, HasMFDerivAt 𝓘(ℝ) AJ (fun s => g (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Z t (g (t,x)))) := hc.2.2.2
  have hd0 (x : X × PlaneFour) : delta eps phi (0,x) = x := by
    simp only [delta,mul_zero,exterior_zero,hzero]
  have ha0 (x : X × SphereFour) : a (0,x) = x := by
    by_cases hx : ∃ i, x ∈ (e i).source
    · obtain ⟨i,hi⟩ := hx
      change insert e (delta eps phi) (0,x) = x
      rw [insert_in_source e hdis _ _ i x hi,hd0,(e i).left_inv hi]
    · exact insert_outside e _ _ _ (not_exists.mp hx)
  have hg0 (x : X × SphereFour) : g (0,x) = x := by
    change a (0,ambientFlow l eps 0 x) = x
    rw [hbz,ha0]
  have hbi (t : ℝ) (x : X × SphereFour) : ambientFlow l eps (-t) (ambientFlow l eps t x) = x := by
    rw [← hbadd,neg_add_cancel,hbz]
  have hbri (t : ℝ) (x : X × SphereFour) : ambientFlow l eps t (ambientFlow l eps (-t) x) = x := by
    rw [← hbadd,add_neg_cancel,hbz]
  let ge : (X × SphereFour) ≃ₘ⟮AJ,AJ⟯ (X × SphereFour) := {
    toFun := fun x => g (1,x)
    invFun := fun x => ambientFlow l eps (-1) (ai (1,x))
    left_inv := by
      intro x
      change ambientFlow l eps (-1) (ai (1,a (1,ambientFlow l eps 1 x))) = x
      exact (congrArg (ambientFlow l eps (-1)) (hal 1 _)).trans (hbi 1 x)
    right_inv := by
      intro x
      change a (1,ambientFlow l eps 1 (ambientFlow l eps (-1) (ai (1,x)))) = x
      rw [hbri]; exact har 1 x
    contMDiff_toFun := hg.comp (contMDiff_const.prodMk contMDiff_id)
    contMDiff_invFun := (hbj.comp (contMDiff_const.prodMk contMDiff_id)).comp
      (hais.comp (contMDiff_const.prodMk contMDiff_id)) }
  let H := Periodization.periodicHamiltonian L
  let Phi := Periodization.periodizedFlow ge g
  let VP := Periodization.periodizedVector Z
  have hPhiEnds := Periodization.periodizedFlow_endpoints ge g hg0
  have hpeq : (fun x => Phi (1,x)) = (fun x => g (1,x)) := funext hPhiEnds.2
  have hgcap : g = CapEnd.closedPath l (by linarith) eps phi := rfl
  have hlocalfix : {x | phi (eps,x) = x} = GenericGeometry.criticalSet (E := LE) F :=
    Set.ext hfix
  have hlocalmap : MapsTo (fun x => phi (eps,x)) (univ ×ˢ box) (univ ×ˢ box) :=
    fun x hx => ⟨mem_univ _,hbox eps x hx.2⟩
  have hsubcrit (x : X × PlaneFour) (hx : phi (eps,x) = x) : x.2 ∈ box :=
    in_box_of_totalSq x.2 (le_of_lt (hcrit x ((hfix x).mp hx)))
  have hfinitel : {x | phi (eps,x) = x}.Finite := hlocalfix.symm ▸ hfinite
  obtain ⟨hgfinite,hgcount⟩ := CapEnd.endpoint_count l eps hl heps hepspi phi hlocalmap hsubcrit hfinitel
  have hgnd := CapEnd.endpoint_nondegenerate (𝓡 4) l eps hl heps hepspi phi
    (by rw [local_charts]; simpa only [local_model] using hphi) hlocalmap
    (by intro x hx; rw [local_charts]; simpa only [Conjugacy.NondegenerateAt,local_model] using
      (ContinuousLinearMap.isUnit_iff_bijective.mp (hnd x hx)))
  refine ⟨wM,H,Phi,VP,hwM,?_,?_,?_,hPhiEnds.1,?_,?_,?_,?_,?_⟩
  · simpa only [ambient_model] using Periodization.periodicHamiltonian_smooth L hL
  · exact Periodization.periodicHamiltonian_periodic L
  · simpa only [ambient_model] using Periodization.periodizedFlow_smooth ge g hg hg0 (fun _ => rfl)
  · intro t x
    ext u
    have hp := congrArg (fun T : AE →L[ℝ] ℝ => T u)
      (Periodization.periodizedVector_hamiltonian wM.form L hL Z hZ t x)
    have heq : mfderiv AI 𝓘(ℝ) (fun y => H (t,y)) x u =
        mfderiv AJ 𝓘(ℝ) (fun y => H (t,y)) x u :=
      congrArg (fun I : ModelWithCorners ℝ AE AE =>
        (show ℝ from mfderiv I 𝓘(ℝ) (fun y => H (t,y)) x u)) ambient_model
    exact hp.trans heq.symm
  · intro t x
    have heq := congrArg (fun model : ModelWithCorners ℝ AE AE =>
      HasMFDerivAt 𝓘(ℝ) model (fun time => Phi (time,x)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (show TangentSpace model (Phi (t,x)) from VP t (Phi (t,x))))) ambient_model
    exact heq.mpr (Periodization.periodizedFlow_ode ge g hg0 (fun _ => rfl) Z hgODE t x)
  · have hp (x : X × SphereFour) : Phi (1,x) = CapEnd.closedPath l (by linarith) eps phi (1,x) := hPhiEnds.2 x
    simpa only [hp] using hgfinite
  · change Nat.card {x // (fun x => Phi (1,x)) x = x} = _
    rw [hpeq,hgcap]
    change {x | CapEnd.closedPath l (by linarith) eps phi (1,x) = x}.ncard =
      16 * (GenericGeometry.criticalSet (E := LE) F).ncard
    simpa only [hlocalfix] using hgcount
  · intro x hx
    have hxg : g (1,x) = x := (hPhiEnds.2 x).symm.trans hx
    have hh := hgnd x (by simpa only [hgcap] using hxg)
    change Conjugacy.NondegenerateAt AI (fun y => Phi (1,y)) x
    rw [hpeq,hgcap]
    exact hh
end
end MorseArnold.CapTransfer

end

end OAI
