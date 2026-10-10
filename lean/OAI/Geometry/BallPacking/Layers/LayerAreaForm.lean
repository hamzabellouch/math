import Mathlib
import OAI.Geometry.BallPacking.Annuli.CylinderAnnularNormalization

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def layerHamiltonian (F H : (ι → ℝ) → ℝ) (ρ : ℝ → ℝ) (p : ℝ × PlanePhase ι) : ℝ :=
  F (planeMoments p.2)+ρ p.1*H (planeMoments p.2)

omit [DecidableEq ι] in
@[fun_prop] theorem layerHamiltonian_smooth {F H : (ι → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (layerHamiltonian F H ρ) :=
  (hF.comp (planeMoments_smooth.comp contDiff_snd)).add
    ((hρ.comp contDiff_fst).mul (hH.comp (planeMoments_smooth.comp contDiff_snd)))

omit [DecidableEq ι] in
private theorem scalar_area_slice {L : Plane → ℝ} {q : Plane} {c : ℝ}
    (hL : DifferentiableAt ℝ L q) (hc : HasDerivAt (fun s => L (s,q.2)) c q.1) :
    fderiv ℝ L q (1,0)=c := by
  have hline := (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hL.hasFDerivAt.comp_hasDerivAt q.1 hline).unique hc

omit [DecidableEq ι] in
theorem areaLayerForm_apply {I : Set ℝ} (hI : IsOpen I) (hconv : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    {F H : (ι → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ)
    {p : Plane × PlanePhase ι} (hp : p.1∈I ×ˢ Ioo (0:ℝ) 1) (v w : Plane × PlanePhase ι) :
    layerForm F (areaLayerCoordinate ℓ a ρ H) p v w=phaseArea v.2 w.2+
      ℓ p.1*(v.1.1*w.1.2-v.1.2*w.1.1)+
      fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) (v.1.1,v.2)*w.1.2-
      v.1.2*fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) (w.1.1,w.2) := by
  let L := layerAreaIntegral ℓ a
  let K : ℝ × PlanePhase ι → ℝ := fun q => ρ q.1*H (planeMoments q.2)
  have hL : DifferentiableAt ℝ L p.1 :=
    ((layerAreaIntegral_smooth hI hconv ha hℓ).contDiffAt ((hI.prod isOpen_Ioo).mem_nhds hp)).differentiableAt (by simp)
  have hK : Differentiable ℝ K := ((hρ.comp contDiff_fst).mul
    (hH.comp (planeMoments_smooth.comp contDiff_snd))).differentiable (by simp)
  have hFs : Differentiable ℝ (toricFunction F) := (hF.comp planeMoments_smooth).differentiable (by simp)
  have hpart : fderiv ℝ L p.1 (1,0)=ℓ p.1 :=
    scalar_area_slice hL (layerAreaIntegral_hasDerivAt hI hconv ha hp.1 hp.2 hℓ)
  have hfd (u : Plane × PlanePhase ι) : fderiv ℝ (areaLayerCoordinate ℓ a ρ H) p u=
      fderiv ℝ L p.1 u.1+fderiv ℝ K (p.1.1,p.2) (u.1.1,u.2) := by
    change fderiv ℝ (baseCoefficient L+firstBaseCoefficient K) p u=_
    have hLD : DifferentiableAt ℝ (baseCoefficient L) p := hL.comp p differentiableAt_fst
    have hKD : DifferentiableAt ℝ (firstBaseCoefficient K) p :=
      (hK _).comp p ((differentiableAt_fst.fst).prodMk differentiableAt_snd)
    rw [fderiv_add hLD hKD]
    simp only [add_apply,baseCoefficient_fderiv_at hL,firstBaseCoefficient_fderiv_at (hK _)]
  have hgd (u : ℝ × PlanePhase ι) : fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) u=
      fderiv ℝ (toricFunction F) p.2 u.2+fderiv ℝ K (p.1.1,p.2) u := by
    change fderiv ℝ ((toricFunction F ∘ Prod.snd)+K) (p.1.1,p.2) u=_
    rw [fderiv_add ((hFs _).comp _ differentiableAt_snd) (hK _),
      fderiv_comp _ (hFs _) differentiableAt_snd]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_snd]
    rfl
  rw [layerForm_apply,hfd,hfd,hgd,hgd,plane_covector_decomp (fderiv ℝ L p.1) v.1,
    plane_covector_decomp (fderiv ℝ L p.1) w.1,hpart]
  ring


end

section

open scoped ContDiff Topology BigOperators
open Set Function

def areaHamiltonianForm {m : ℕ} (ℓ : Plane → ℝ) (G : ℝ × PlanePhase (Fin m) → ℝ)
    (p : Plane × PlanePhase (Fin m)) :
    (Plane × PlanePhase (Fin m)) →L[ℝ] (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase (Fin m)))
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase (Fin m)))
  let c := ds.prod (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))
  let β := (fderiv ℝ G (p.1.1,p.2)).comp c
  phaseArea.bilinearComp (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))
      (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))+
    ℓ p.1 • (ds.smulRight dt-dt.smulRight ds)+β.smulRight dt-dt.smulRight β

@[simp] theorem areaHamiltonianForm_apply {m : ℕ} (ℓ : Plane → ℝ)
    (G : ℝ × PlanePhase (Fin m) → ℝ) (p v w : Plane × PlanePhase (Fin m)) :
    areaHamiltonianForm ℓ G p v w=phaseArea v.2 w.2+ℓ p.1*(v.1.1*w.1.2-v.1.2*w.1.1)+
      fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*w.1.2-v.1.2*fderiv ℝ G (p.1.1,p.2) (w.1.1,w.2) := by
  simp [areaHamiltonianForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem areaHamiltonianForm_layer {m : ℕ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a b : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    {F H : (Fin m → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    {G : ℝ × PlanePhase (Fin m) → ℝ}
    (he : ∀ s∈Ioo a b,∀ v,planeMoments v∈V→G (s,v)=layerHamiltonian F H ρ (s,v))
    {p : Plane × PlanePhase (Fin m)}
    (hp : p∈(Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) :
    areaHamiltonianForm ℓ G p=layerForm F (areaLayerCoordinate ℓ a ρ H) p := by
  have hseg : Icc a b⊆I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  have hgerm : G =ᶠ[nhds (p.1.1,p.2)] layerHamiltonian F H ρ := by
    filter_upwards [(isOpen_Ioo.prod hV).mem_nhds ⟨hp.1.1,hp.2⟩] with q hq
    exact he q.1 hq.1 q.2 hq.2
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [areaHamiltonianForm_apply,areaLayerForm_apply hI hc ha hℓ hF hH hρ
    ⟨hseg ⟨hp.1.1.1.le,hp.1.1.2.le⟩,hp.1.2⟩,hgerm.fderiv_eq]

theorem finite_area_layer_packing {m : ℕ} {ι : Type*}
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q)
    (F H : ι → (Fin m → ℝ) → ℝ) (ρ : ι → ℝ → ℝ)
    (hF : ∀ i,ContDiff ℝ ∞ (F i)) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    (hρ : ∀ i,ContDiff ℝ ∞ (ρ i)) (hρpos : ∀ i s,0≤deriv (ρ i) s)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (hHp : ∀ i p,p∈V→0≤H i p)
    (a b r r' : ι → ℝ) (ha : ∀ i,a i∈I) (hb : ∀ i,b i∈I) (hab : ∀ i,a i<b i)
    (hρa : ∀ i,ρ i (a i)=0) (hρb : ∀ i,ρ i (b i)=1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j)→(∑ j,p j)≤r' i→p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p)
    (G : ℝ × PlanePhase (Fin m) → ℝ)
    (he : ∀ i,∀ s∈Ioo (a i) (b i),∀ v,planeMoments v∈V→
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i) (s,v)) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
      (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v w,areaHamiltonianForm ℓ G (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z w)=standardForm v w) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  have hd i := areaLayerCoordinate_data hI hc (ha i) (hb i) (hab i) hℓ hpos
    (hρ i) (hρpos i) (hρa i) (hρb i) (hH i) (hHp i)
  exact finite_layer_packing_local F H (fun i => areaLayerCoordinate ℓ (a i) (ρ i) (H i))
    hF hV a b r r' hab (fun i => (hd i).1) hdis (fun i => (hd i).2.1)
    (fun i => (hd i).2.2.1) (fun i => (hd i).2.2.2) hr' hrr hsimplex hheight
    (areaHamiltonianForm ℓ G) (fun i _ hp => areaHamiltonianForm_layer hI hc (ha i) (hb i)
      (hab i) hℓ (hF i) (hH i) (hρ i) hV (he i) hp)


end

section
open scoped ContDiff Topology
open Set Function

theorem normalizedAreaDensity_smooth {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {A B : Plane → ℝ} (hA : ContDiffOn ℝ ∞ A (I ×ˢ J)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ J))
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1))
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) :
    ContDiffOn ℝ ∞ (normalizedAreaDensity A B g) (I ×ˢ Ioo (0:ℝ) 1) := by
  have hq : ContDiffOn ℝ ∞ (fun q : Plane => (q.1,g q.2)) (I ×ˢ Ioo (0:ℝ) 1) :=
    contDiffOn_fst.prodMk (hg.comp contDiffOn_snd (fun _ h => h.2))
  have hqm : MapsTo (fun q : Plane => (q.1,g q.2)) (I ×ˢ Ioo (0:ℝ) 1) (I ×ˢ J) :=
    fun _ h => ⟨h.1,hmap h.2⟩
  exact ((((hB.fderiv_of_isOpen (hI.prod hJ) (by simp)).comp hq hqm).clm_apply contDiffOn_const).sub
    (((hA.fderiv_of_isOpen (hI.prod hJ) (by simp)).comp hq hqm).clm_apply contDiffOn_const)).mul
    ((hg.deriv_of_isOpen isOpen_Ioo (by simp)).comp contDiffOn_snd (fun _ h => h.2))

theorem normalizedAreaDensity_pos {I J : Set ℝ} {A B : Plane → ℝ} {g : ℝ → ℝ}
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) (hg : ∀ T∈Ioo (0:ℝ) 1,0<deriv g T)
    (hbase : ∀ q∈I ×ˢ J,0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    {q : Plane} (hq : q∈I ×ˢ Ioo (0:ℝ) 1) : 0<normalizedAreaDensity A B g q :=
  mul_pos (hbase _ ⟨hq.1,hmap hq.2⟩) (hg _ hq.2)

theorem exists_normalized_positive_area {b : ℝ} (hb : 0<b) (hsmall : b<1/2)
    {I : Set ℝ} (hI : IsOpen I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ Ioo (1/2-b) (1/2+b)))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ Ioo (1/2-b) (1/2+b)))
    (hbase : ∀ q∈I ×ˢ Ioo (1/2-b) (1/2+b),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1)) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      MapsTo g (Ioo (0:ℝ) 1) (Ioo (1/2-b) (1/2+b)) ∧
      (∀ t∈Ioo (1/2-b) (1/2+b),g (intervalClock (-b) b (t-1/2))=t) ∧
      (∀ T∈Ioo (0:ℝ) 1,intervalClock (-b) b (g T-1/2)=T) ∧
      (∀ T∈Ioo (0:ℝ) 1,positiveCircleClock b (circleTurn (g T))*deriv g T=1) ∧
      ContDiffOn ℝ ∞ (normalizedAreaDensity A B g) (I ×ˢ Ioo (0:ℝ) 1) ∧
      (∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<normalizedAreaDensity A B g q) := by
  obtain ⟨g,hg,hm,hl,hr,hd⟩ := positiveCircleClock_inverse hb hsmall
  refine ⟨g,hg,fun _ h => hm _ h,hl,hr,fun T hT => (hd T hT).2,
    normalizedAreaDensity_smooth hI isOpen_Ioo hA hB hg (fun _ h => hm _ h),?_⟩
  intro q hq
  exact normalizedAreaDensity_pos (fun _ h => hm _ h) (fun T hT => (hd T hT).1) hbase hq


end

section

open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem angularReparam_smoothOn {g : ℝ → ℝ} {J : Set ℝ} (hg : ContDiffOn ℝ ∞ g J)
    {U : Set (Plane × E)} (hU : ∀ p∈U,p.1.2∈J) : ContDiffOn ℝ ∞ (angularReparam g) U :=
  ((contDiff_fst.comp contDiff_fst).contDiffOn.prodMk
    (hg.comp (contDiff_snd.comp contDiff_fst).contDiffOn hU)).prodMk contDiff_snd.contDiffOn

theorem angularReparam_isEmbedding {g C : ℝ → ℝ} {J : Set ℝ}
    (hg : ContDiffOn ℝ ∞ g J) (hC : Continuous C) (hinv : ∀ T∈J,C (g T)=T)
    {U : Set (Plane × E)} (hU : ∀ p∈U,p.1.2∈J) :
    Topology.IsEmbedding (fun p : U => angularReparam g p.val) := by
  have hs : Continuous (fun p : U => angularReparam g p.val) :=
    (angularReparam_smoothOn hg hU).continuousOn.domRestrict
  have hCs : Continuous (angularReparam (E := E) C) :=
    (continuous_fst.fst.prodMk (hC.comp continuous_fst.snd)).prodMk continuous_snd
  have he : angularReparam (E := E) C ∘ (fun p : U => angularReparam g p.val)=Subtype.val := by
    funext p
    change ((p.val.1.1,C (g p.val.1.2)),p.val.2)=p.val
    rw [hinv _ (hU _ p.property)]
  apply Topology.IsEmbedding.of_comp hs hCs
  rw [he]
  exact Topology.IsEmbedding.subtypeVal

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem angularReparam_injOn {g C : ℝ → ℝ} {J : Set ℝ}
    (hinv : ∀ T∈J,C (g T)=T) {U : Set (Plane × E)} (hU : ∀ p∈U,p.1.2∈J) :
    InjOn (angularReparam g) U := by
  intro p hp q hq he
  have hh := congrArg (angularReparam (E := E) C) he
  change ((p.1.1,C (g p.1.2)),p.2)=((q.1.1,C (g q.1.2)),q.2) at hh
  simpa only [hinv _ (hU _ hp),hinv _ (hU _ hq)] using hh


end

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem angular_packing_transport {m : ℕ} {ι : Type*} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ J)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ J))
    {w g C : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1))
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) (hC : Continuous C)
    (hinv : ∀ T∈Ioo (0:ℝ) 1,C (g T)=T)
    (hnorm : ∀ T∈Ioo (0:ℝ) 1,w (g T)*deriv g T=1)
    {G : ℝ × PlanePhase (Fin m) → ℝ} (hG : ContDiff ℝ ∞ G)
    (a b r : ι → ℝ) (ha : ∀ i,Ioo (a i) (b i)⊆I) {V : Set (Fin m → ℝ)}
    (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m))
    (hU : ∀ i,IsOpen (U i)) (hBU : ∀ i,closedBall (m+1) (r i)⊆U i)
    (hφ : ∀ i,ContDiffOn ℝ ∞ (φ i) (U i))
    (hemb : ∀ i,Topology.IsEmbedding (fun z : U i => φ i z))
    (him : ∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V))
    (hform : ∀ i,∀ z∈U i,∀ v u,
      areaHamiltonianForm (normalizedAreaDensity A B g) G (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u)
    (hdis : Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r i))
      (φ j '' closedBall (m+1) (r j)))) :
    ∃ ψ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m),
      (∀ i,ContDiffOn ℝ ∞ (ψ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => ψ i z)) ∧
      (∀ i,∀ z∈U i,ψ i z∈(Ioo (a i) (b i) ×ˢ J) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v u,
        horizontalCoupling phaseArea (baseCoefficient A) (weightedSecondCoefficient B (fun q => w q.2) G)
          (ψ i z) (fderiv ℝ (ψ i) z v) (fderiv ℝ (ψ i) z u)=standardForm v u) ∧
      Pairwise (fun i j => Disjoint (ψ i '' closedBall (m+1) (r i))
        (ψ j '' closedBall (m+1) (r j))) := by
  let S : Set (Plane × PlanePhase (Fin m)) := (I ×ˢ Ioo (0:ℝ) 1) ×ˢ (Set.univ : Set (PlanePhase (Fin m)))
  have hS : IsOpen S := (hI.prod isOpen_Ioo).prod isOpen_univ
  have hmS : ∀ i,MapsTo (φ i) (U i) S := fun i z hz =>
    ⟨⟨ha i (him i z hz).1.1,(him i z hz).1.2⟩,mem_univ _⟩
  have hgs : ContDiffOn ℝ ∞ (angularReparam g) S := angularReparam_smoothOn hg (fun _ h => h.1.2)
  let ψ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m) := fun i => angularReparam g ∘ φ i
  have hψ : ∀ i,ContDiffOn ℝ ∞ (ψ i) (U i) := fun i => hgs.comp (hφ i) (hmS i)
  have hCs : Continuous (angularReparam (E := PlanePhase (Fin m)) C) :=
    (continuous_fst.fst.prodMk (hC.comp continuous_fst.snd)).prodMk continuous_snd
  refine ⟨ψ,hψ,?_,?_,?_,?_⟩
  · intro i
    have he : angularReparam (E := PlanePhase (Fin m)) C ∘ (fun z : U i => ψ i z)=
        (fun z : U i => φ i z) := by
      funext z
      change (((φ i z).1.1,C (g (φ i z).1.2)),(φ i z).2)=φ i z
      rw [hinv _ (him i z z.property).1.2]
    apply Topology.IsEmbedding.of_comp (hψ i).continuousOn.domRestrict hCs
    change Topology.IsEmbedding (angularReparam C ∘ (fun z : U i => ψ i z))
    rw [he]
    exact hemb i
  · intro i z hz
    exact ⟨⟨(him i z hz).1.1,hmap (him i z hz).1.2⟩,(him i z hz).2⟩
  · intro i z hz v u
    have hp := hmS i hz
    have hq : ((φ i z).1.1,g (φ i z).1.2)∈I ×ˢ J := ⟨hp.1.1,hmap hp.1.2⟩
    have hgd := (hg.contDiffAt (isOpen_Ioo.mem_nhds hp.1.2)).differentiableAt (by simp)
    have hψd : fderiv ℝ (ψ i) z=
        (fderiv ℝ (angularReparam g) (φ i z)).comp (fderiv ℝ (φ i) z) :=
      fderiv_comp z ((hgs.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))
        (((hφ i).contDiffAt ((hU i).mem_nhds hz)).differentiableAt (by simp))
    rw [hψd]
    simp only [ContinuousLinearMap.comp_apply]
    dsimp only [ψ,Function.comp_apply]
    rw [angularReparam_weighted_pullback phaseArea
      ((hA.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by simp))
      ((hB.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by simp))
      (hw.differentiable (by simp) _) hgd (hG.differentiable (by simp) _) (hnorm _ hp.1.2)]
    simpa only [areaHamiltonianForm_apply] using hform i z hz v u
  · intro i j hij
    rw [show ψ i=angularReparam g ∘ φ i from rfl,show ψ j=angularReparam g ∘ φ j from rfl,
      Set.image_comp,Set.image_comp]
    apply (hdis hij).image (angularReparam_injOn hinv (fun _ hp => hp.1.2) (U := S))
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS i (hBU i hz)
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS j (hBU j hz)

theorem finite_weighted_layer_packing {m : ℕ} {ι : Type*}
    {δ : ℝ} (hδ : 0<δ) (hsmall : δ<1/2)
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hbase : ∀ q∈I ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    (F H : ι → (Fin m → ℝ) → ℝ) (ρ : ι → ℝ → ℝ)
    (hF : ∀ i,ContDiff ℝ ∞ (F i)) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    (hρ : ∀ i,ContDiff ℝ ∞ (ρ i)) (hρpos : ∀ i s,0≤deriv (ρ i) s)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (hHp : ∀ i p,p∈V→0≤H i p)
    (a b r r' : ι → ℝ) (ha : ∀ i,a i∈I) (hb : ∀ i,b i∈I) (hab : ∀ i,a i<b i)
    (hρa : ∀ i,ρ i (a i)=0) (hρb : ∀ i,ρ i (b i)=1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p)
    (G : ℝ × PlanePhase (Fin m) → ℝ) (hG : ContDiff ℝ ∞ G)
    (he : ∀ i,∀ s∈Ioo (a i) (b i),∀ v,planeMoments v∈V →
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i) (s,v)) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
      (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v u,
        horizontalCoupling phaseArea (baseCoefficient A)
          (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2)) G)
          (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨g,hg,hm,_,hinv,hnorm,hℓ,hpos⟩ := exists_normalized_positive_area hδ hsmall hI hA hB hbase
  obtain ⟨U,φ,hU,hBU,hφ,hemb,him,hform,hdi⟩ := finite_area_layer_packing hI hc hℓ hpos F H ρ
    hF hH hρ hρpos hV hHp a b r r' ha hb hab hρa hρb hdis hr' hrr hsimplex hheight G he
  have hw : ContDiff ℝ ∞ (fun t => positiveCircleClock δ (circleTurn t)) :=
    ((positiveCircleClock_smooth hδ hsmall).comp circleTurn_smooth).contDiff
  have hC : Continuous (fun t => intervalClock (-δ) δ (t-1/2)) :=
    (intervalClock_smooth (-δ) δ).continuous.comp (continuous_id.sub continuous_const)
  have hasub : ∀ i,Ioo (a i) (b i)⊆I := by
    intro i
    have hseg : Icc (a i) (b i)⊆I := by
      simpa only [segment_eq_uIcc,uIcc_of_le (hab i).le] using hc.segment_subset (ha i) (hb i)
    exact Ioo_subset_Icc_self.trans hseg
  obtain ⟨ψ,hψ,heψ,hiψ,hfψ,hdψ⟩ := angular_packing_transport hI isOpen_Ioo hA hB hw hg hm hC
    hinv hnorm hG a b r' hasub U φ hU hBU hφ hemb him hform hdi
  exact ⟨U,ψ,hU,hBU,hψ,heψ,hiψ,hfψ,hdψ⟩


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def surfaceRemainder (K H : E → ℝ) (h : ι → E → ℝ) (ψ : E → E) (v : E) : ℝ :=
  K (ψ v)-K v+H v-∑ i, h i v

@[fun_prop] theorem surfaceRemainder_smooth {K H : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) (hh : ∀ i, ContDiff ℝ ∞ (h i))
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (surfaceRemainder K H h ψ) := by
  exact ((hK.comp hψ).sub hK |>.add hH).sub (ContDiff.sum (fun i _ => hh i))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem surfaceRemainder_gap {K H H₀ C : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    {g ε : ℝ} {v : E} (hgap : g ≤ K (ψ v)-K v+H₀ v-C v)
    (harea : |H v-H₀ v| < 2*ε) (hcap : (∑ i, h i v)-C v < ε) :
    g-3*ε < surfaceRemainder K H h ψ v := by
  have ha := (abs_lt.mp harea).1
  dsimp [surfaceRemainder]
  linarith

def surfaceFirstLayer (S : ℝ → ℝ) (H : E → ℝ) (ψ : E → E) (p : ℝ × E) : ℝ :=
  S p.1*H (ψ p.2)

def surfaceFinalLayer (J : E → ℝ) (h : ι → E → ℝ) (R : E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (p : ℝ × E) : ℝ :=
  J p.2+(∑ i, ρ i p.1*h i p.2)+ρ₀ p.1*R p.2

@[fun_prop] theorem surfaceFirstLayer_smooth {S : ℝ → ℝ} {H : E → ℝ} {ψ : E → E}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (surfaceFirstLayer S H ψ) :=
  (hS.comp contDiff_fst).mul ((hH.comp hψ).comp contDiff_snd)

@[fun_prop] theorem surfaceFinalLayer_smooth {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) : ContDiff ℝ ∞ (surfaceFinalLayer J h R ρ ρ₀) :=
  ((hJ.comp contDiff_snd).add (ContDiff.sum (fun i _ =>
    (hρ i |>.comp contDiff_fst).mul (hh i |>.comp contDiff_snd)))).add
    ((hρ₀.comp contDiff_fst).mul (hR.comp contDiff_snd))

theorem first_partial_eq_deriv {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (1,0)=deriv (fun s => F (s,p.2)) p.1 := by
  exact (hF.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv.symm

theorem surfaceFirstLayer_firstDerivative {S : ℝ → ℝ} {H : E → ℝ} {ψ : E → E}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) (hψ : ContDiff ℝ ∞ ψ) (p : ℝ × E) :
    fderiv ℝ (surfaceFirstLayer S H ψ) p (1,0)=deriv S p.1*H (ψ p.2) := by
  rw [first_partial_eq_deriv ((surfaceFirstLayer_smooth hS hH hψ).differentiable (by simp) p)]
  simpa only [surfaceFirstLayer] using ((hS.differentiable (by simp) p.1).hasDerivAt.mul_const (H (ψ p.2))).deriv

theorem surfaceFinalLayer_firstDerivative {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (p : ℝ × E) :
    fderiv ℝ (surfaceFinalLayer J h R ρ ρ₀) p (1,0)=
      (∑ i, deriv (ρ i) p.1*h i p.2)+deriv ρ₀ p.1*R p.2 := by
  rw [first_partial_eq_deriv ((surfaceFinalLayer_smooth hJ hR hh hρ hρ₀).differentiable (by simp) p)]
  have hd := ((hasDerivAt_const p.1 (J p.2)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ => (hρ i |>.differentiable (by simp) p.1).hasDerivAt.mul_const (h i p.2)))).add
    ((hρ₀.differentiable (by simp) p.1).hasDerivAt.mul_const (R p.2))
  have he : (((fun _ : ℝ => J p.2) + ∑ i, fun s => ρ i s*h i p.2) +
      fun s => ρ₀ s*R p.2) = fun s => surfaceFinalLayer J h R ρ ρ₀ (s,p.2) := by
    funext s
    simp [surfaceFinalLayer]
  rw [he] at hd
  simpa only [zero_add] using hd.deriv

theorem surfaceFinalLayer_firstDerivative_nonneg {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (hm : ∀ i, Monotone (ρ i)) (hm₀ : Monotone ρ₀)
    (p : ℝ × E) (hpos : ∀ i, 0 ≤ h i p.2) (hRpos : 0 ≤ R p.2) :
    0 ≤ fderiv ℝ (surfaceFinalLayer J h R ρ ρ₀) p (1,0) := by
  rw [surfaceFinalLayer_firstDerivative hJ hR hh hρ hρ₀]
  exact add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hm i |>.deriv_nonneg) (hpos i)))
    (mul_nonneg hm₀.deriv_nonneg hRpos)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem surfaceFinalLayer_lower {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {s : ℝ} (hz : ∀ i, ρ i s=0) (hz₀ : ρ₀ s=0) (v : E) :
    surfaceFinalLayer J h R ρ ρ₀ (s,v)=J v := by simp [surfaceFinalLayer,hz,hz₀]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem surfaceFinalLayer_upper {K H : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {s : ℝ} (ho : ∀ i, ρ i s=1) (ho₀ : ρ₀ s=1) (v : E) :
    surfaceFinalLayer (K-H) h (surfaceRemainder K H h ψ) ρ ρ₀ (s,v)=K (ψ v) := by
  simp only [surfaceFinalLayer,surfaceRemainder,ho,ho₀,Pi.sub_apply,one_mul]
  ring


end

open scoped ContDiff
open Set Function

theorem surfaceFinalLayer_on_ordered_interval {N : ℕ} {E : Type*}
    (J R : E → ℝ) (h : Fin N → E → ℝ)
    {lo hi : Fin (N+1) → ℝ} {ρ : Fin (N+1) → ℝ → ℝ}
    (hord : ∀ i j, i < j → hi i < lo j)
    (hends : ∀ i, (∀ s, s ≤ lo i → ρ i s=0) ∧ (∀ s, hi i ≤ s → ρ i s=1))
    (i : Fin N) {s : ℝ} (hs : s ∈ Icc (lo i.castSucc) (hi i.castSucc)) (v : E) :
    surfaceFinalLayer J h R (fun j => ρ j.castSucc) (ρ (Fin.last N)) (s,v)=
      J v+(∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), h j v)+ρ i.castSucc s*h i v := by
  classical
  have hlast : ρ (Fin.last N) s=0 := (hends _).1 s (hs.2.trans (hord _ _ (by simp)).le)
  have he (j : Fin N) : ρ j.castSucc s*h j v =
      (if j < i then h j v else 0)+(if j=i then ρ i.castSucc s*h i v else 0) := by
    rcases lt_trichotomy j i with hj | hj | hj
    · have hr : ρ j.castSucc s=1 := (hends _).2 s ((hord _ _ (by simpa using hj)).le.trans hs.1)
      simp [hj,ne_of_lt hj,hr]
    · subst j
      simp
    · have hr : ρ j.castSucc s=0 := (hends _).1 s (hs.2.trans (hord _ _ (by simpa using hj)).le)
      simp [not_lt.mpr hj.le,ne_of_gt hj,hr]
  unfold surfaceFinalLayer
  rw [hlast,zero_mul,add_zero]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => he j)]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_filter]
  simp
  ring

theorem exists_surface_layer_clocks (N : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
      (∀ i, a<lo i ∧ lo i<hi i ∧ hi i<b) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ i, ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s, 0 ≤ ρ i s ∧ ρ i s ≤ 1 ∧ 0 ≤ deriv (ρ i) s) ∧
      (∀ i, ∃ δ : ℝ, 0<δ ∧
        (∀ s, s ≤ lo i+δ → ρ i s=0) ∧ (∀ s, hi i-δ ≤ s → ρ i s=1)) ∧
      (∀ (E : Type) (J R : E → ℝ) (h : Fin N → E → ℝ) (i : Fin N) s,
        s ∈ Icc (lo i.castSucc) (hi i.castSucc) → ∀ v,
        surfaceFinalLayer J h R (fun j => ρ j.castSucc) (ρ (Fin.last N)) (s,v)=
          J v+(∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), h j v)+ρ i.castSucc s*h i v) := by
  obtain ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol⟩ := exists_ordered_smooth_clocks (N+1) hab
  refine ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,?_⟩
  intro E J R h i s hs v
  apply surfaceFinalLayer_on_ordered_interval J R h hord _ i hs v
  intro j
  obtain ⟨δ,hδ,hz,ho⟩ := hcol j
  exact ⟨fun s hs => hz s (by linarith),fun s hs => ho s (by linarith)⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
