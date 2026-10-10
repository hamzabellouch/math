import Mathlib
import OAI.Geometry.BallPacking.Layers.LayerBallEmbedding

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem stripChart_fderiv_at {f : Plane × PlanePhase ι → ℝ} (p : Plane × PlanePhase ι) (hf : ContDiffAt ℝ ∞ f p)
    (v : Plane × PlanePhase ι) : fderiv ℝ (stripChart f) p v = ((fderiv ℝ f p v,v.1.2),v.2) := by
  have hd := (((hf.differentiableAt (by simp)).hasFDerivAt).prodMk
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (stripChart f) _ p at hd
  rw [hd.fderiv]
  rfl

theorem layerChart_pullback_at {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (p : Plane × PlanePhase ι) (hf : ContDiffAt ℝ ∞ f p) (v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (layerChart F f) p v)
      (fderiv ℝ (layerChart F f) p w) = layerForm F f p v w := by
  have hs : DifferentiableAt ℝ (stripChart f) p :=
    ((hf.prodMk (contDiffAt_snd.comp p contDiffAt_fst)).prodMk contDiffAt_snd).differentiableAt (by simp)
  rw [layerChart,fderiv_comp p ((toricSuspension_smooth hF).differentiable (by simp) _)
    hs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [toricSuspension_pullback hF,stripChart_fderiv_at p hf,stripChart_fderiv_at p hf,
    oneCovectorForm_apply,layerForm_apply]
  change phaseArea v.2 w.2 + 1*(fderiv ℝ f p v*w.1.2-v.1.2*fderiv ℝ f p w) +
    fderiv ℝ (toricFunction F) p.2 v.2*w.1.2-v.1.2*fderiv ℝ (toricFunction F) p.2 w.2 = _
  ring

theorem layerChart_inverse_local {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v)) :
    ∃ (W : Set (Plane × PlanePhase ι)) (g : Plane × PlanePhase ι → Plane × PlanePhase ι),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = layerChart F f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → planeMoments p.2 ∈ V →
        0 < p.1.1 → p.1.1 < H (planeMoments p.2) → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V), g (layerChart F f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V) ∧ layerChart F f (g p) = p) := by
  obtain ⟨W,g,hWo,hgs,hWe,hav,hl,hr⟩ := stripChart_inverse_local hV hab hf (H ∘ planeMoments) hderiv hlo hhi
  let e := toricSuspensionHomeomorph hF
  let G := g ∘ toricSuspensionInverse F
  have hpre : e.symm ⁻¹' W = e '' W := by
    ext p
    exact ⟨fun hp => ⟨e.symm p,hp,e.apply_symm_apply p⟩,by rintro ⟨p,hp,rfl⟩; simpa using hp⟩
  refine ⟨e '' W,G,e.isOpen_image.mpr hWo,?_,?_,?_,?_,?_⟩
  · apply hgs.comp (toricSuspensionInverse_smooth hF).contDiffOn
    intro p hp
    change p ∈ e.symm ⁻¹' W
    rw [hpre]
    exact hp
  · rw [hWe,←image_comp]
    rfl
  · intro p hpT hpV hp0 hpH
    refine ⟨e.symm p,?_,e.apply_symm_apply p⟩
    apply hav (e.symm p) hpT
    · change planeMoments (toricSuspensionInverse F p).2 ∈ V
      simpa only [toricSuspensionInverse_moments] using hpV
    · exact hp0
    · change p.1.1 < H (planeMoments (toricSuspensionInverse F p).2)
      simpa using hpH
  · intro p hp
    change g (toricSuspensionInverse F (toricSuspension F (stripChart f p))) = p
    rw [toricSuspensionInverse_left]
    exact hl p hp
  · rintro p ⟨z,hz,rfl⟩
    have hge : G (e z) = g z := by
      change g (toricSuspensionInverse F (toricSuspension F z)) = g z
      rw [toricSuspensionInverse_left]
    rw [hge]
    refine ⟨(hr z hz).1,?_⟩
    change toricSuspension F (stripChart f (g z)) = toricSuspension F z
    rw [(hr z hz).2]


end

section
open scoped ContDiff Topology BigOperators
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem inverse_layer_product_pullback_local {F : (ι → ℝ) → ℝ}
    {g : Plane × PlanePhase ι → Plane × PlanePhase ι}
    {f₀ : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {U W : Set (Plane × PlanePhase ι)} (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f₀ U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ layerChart F f₀ (g y) = y)
    {q : Plane ≃ₜ Plane} (hqs : ContDiff ℝ ∞ q)
    (hqform : ∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w)
    {z : Plane × PlanePhase ι} (hz : planarProduct q z ∈ W) (v w : Plane × PlanePhase ι) :
    layerForm F f₀ ((g ∘ planarProduct q) z)
      (fderiv ℝ (g ∘ planarProduct q) z v) (fderiv ℝ (g ∘ planarProduct q) z w) =
      productForm phaseArea v w := by
  exact inverse_chart_composition_pullback
    (E := Plane × PlanePhase ι) (f := layerChart F f₀) (g := g)
    (q := (planarProduct q : Plane × PlanePhase ι → Plane × PlanePhase ι))
    (U := U) (W := W) hU hW
    ((toricSuspension_smooth hF).contDiffOn.comp
      ((hf.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn) (fun _ _ => mem_univ _)) hg hr (layerForm F f₀) (productForm phaseArea)
    (fun x hx u t => layerChart_pullback_at hF x (hf.contDiffAt (hU.mem_nhds hx)) u t) (planarProduct_smooth (E := PlanePhase ι) (q := q) hqs)
    (fun x u t => planarProduct_pullback (E := PlanePhase ι) (q := q) hqs hqform (phaseArea (ι := ι)) x u t) hz v w

theorem exists_ball_in_layer_local {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v))
    {r r' : ℝ} (hr' : 0 ≤ r') (hrr : r' < r)
    (hsimplex : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) ≤ r' → p ∈ V)
    (hheight : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → p ∈ V → r-∑ i, p i ≤ H p) :
    ∃ (N : Set (Plane × PlanePhase ι)) (φ : Plane × PlanePhase ι → Plane × PlanePhase ι),
      IsOpen N ∧ splitCapacityBall r' ⊆ N ∧ ContDiffOn ℝ ∞ φ N ∧
      Topology.IsEmbedding (fun z : N => φ z) ∧
      (∀ z ∈ N, φ z ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ z ∈ N, ∀ v w, layerForm F f (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w) =
        productForm phaseArea v w) := by
  let U := (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).prod hV
  have hfU : ContDiffOn ℝ ∞ f U := hf.mono
    (prod_mono (prod_mono Ioo_subset_Icc_self Subset.rfl) Subset.rfl)
  have hchart : ContDiffOn ℝ ∞ (layerChart F f) U :=
    (toricSuspension_smooth hF).contDiffOn.comp
      ((hfU.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn)
      (fun _ _ => mem_univ _)
  obtain ⟨W,g,hW,hg,himage,ha,hl,hr⟩ := layerChart_inverse_local hF hV hab hf H hderiv hlo hhi
  let δ := (r-r')/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : r'+δ < r := by dsimp [δ]; linarith
  obtain ⟨q,hqs,_,hqform,hqbound⟩ := exists_thin_planar_embedding hr' hδ
  let Q : (Plane × PlanePhase ι) ≃ₜ (Plane × PlanePhase ι) := planarProduct q
  have hQ : ContDiff ℝ ∞ Q := planarProduct_smooth hqs
  let N := Q ⁻¹' W
  let φ := g ∘ Q
  have hN : IsOpen N := hW.preimage Q.continuous
  have hball : splitCapacityBall r' ⊆ N := by
    intro z hz
    have hsum : 0 ≤ ∑ i, planeMoments z.2 i :=
      Finset.sum_nonneg (fun i _ => planeMoments_nonneg z.2 i)
    have hz' : radialArea z.1 + ∑ i, planeMoments z.2 i ≤ r' := hz
    have hrad : radialArea z.1 ≤ r' := by linarith
    have hps : (∑ i, planeMoments z.2 i) ≤ r' := by linarith [radialArea_nonneg z.1]
    have hpV := hsimplex (planeMoments z.2) (planeMoments_nonneg z.2) hps
    have hqb := hqbound z.1 hrad
    apply ha (Q z) hqb.2.2 hpV hqb.1
    change (q z.1).1 < H (planeMoments z.2)
    have hh := hheight (planeMoments z.2) (planeMoments_nonneg z.2) hpV
    linarith [hqb.2.1]
  have hsφ : ContDiffOn ℝ ∞ φ N := hg.comp hQ.contDiffOn (fun _ hz => hz)
  have hge : Topology.IsEmbedding (fun y : W => g y) :=
    inverse_chart_isEmbedding hchart.continuousOn
      hg.continuousOn himage.symm hl hr
  let j : N → W := fun z => ⟨Q z,z.property⟩
  have hje : Topology.IsEmbedding j :=
    (Q.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict W (fun z => z.property)
  refine ⟨N,φ,hN,hball,hsφ,hge.comp hje,?_,?_⟩
  · intro z hz
    exact (hr (Q z) hz).1
  · intro z hz v w
    exact inverse_layer_product_pullback_local hF hU hW hfU hg hr hqs hqform hz v w


end

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem finite_layer_packing_local {m : ℕ} {ι : Type*}
    (F H : ι → (Fin m → ℝ) → ℝ)
    (f : ι → Plane × PlanePhase (Fin m) → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i))
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (a b r r' : ι → ℝ) (hab : ∀ i, a i < b i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i)
      ((Icc (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hderiv : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo (a i) (b i),
      0 < deriv (fun u => f i ((u,T),v)) s)
    (hlo : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f i ((a i,T),v) = 0)
    (hhi : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V →
      H i (planeMoments v) < f i ((b i,T),v))
    (hr' : ∀ i, 0 ≤ r' i) (hrr : ∀ i, r' i < r i)
    (hsimplex : ∀ i, ∀ p : Fin m → ℝ, (∀ j, 0 ≤ p j) → (∑ j, p j) ≤ r' i → p ∈ V)
    (hheight : ∀ i, ∀ p : Fin m → ℝ, (∀ j, 0 ≤ p j) → p ∈ V → r i - ∑ j, p j ≤ H i p)
    (Ω : Plane × PlanePhase (Fin m) → (Plane × PlanePhase (Fin m)) →L[ℝ]
      (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ)
    (hΩ : ∀ i, ∀ z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V),
      Ω z = layerForm (F i) (f i) z) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i, IsOpen (U i)) ∧ (∀ i, closedBall (m+1) (r' i) ⊆ U i) ∧
      (∀ i, ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i, Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i, ∀ z ∈ U i, φ i z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i, ∀ z ∈ U i, ∀ v w, Ω (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z w) = standardForm v w) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  classical
  choose N q hN hb hq he him hfq using fun i =>
    exists_ball_in_layer_local (hF i) hV (hab i) (hf i) (H i)
      (hderiv i) (hlo i) (hhi i) (hr' i) (hrr i) (hsimplex i) (hheight i)
  choose U hU hBU hsU heU hiU hfU using fun i =>
    complex_ball_of_split_embedding (hN i) (hb i) (hq i) (he i) (hfq i)
  let φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m) := fun i => q i ∘ complexSplitPhase m
  have himage : ∀ i, ∀ z ∈ U i,
      φ i z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V) := by
    intro i z hz
    obtain ⟨y,hy,heq⟩ := hiU i z hz
    change q i (complexSplitPhase m z) ∈ _
    rw [←heq]
    exact him i y hy
  refine ⟨U,φ,hU,hBU,hsU,heU,himage,?_,?_⟩
  · intro i z hz v w
    rw [hΩ i _ (himage i z hz)]
    exact hfU i z hz v w
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have hi := himage i x (hBU i hx)
    have hj := himage j y (hBU j hy)
    rw [heq] at hj
    exact Set.disjoint_left.mp (hdis hij) hi.1.1 hj.1.1


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_parameter_segment_integral {f : P × ℝ → ℝ} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : ℝ) (p : P × ℝ)
    (hseg : ∀ s ∈ Icc (0:ℝ) 1, (p.1,a+s*(p.2-a)) ∈ U) :
    ContDiffAt ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) p := by
  let K : Set (P × ℝ) := (fun s : ℝ => (p.1,a+s*(p.2-a))) '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.prodMk (continuous_const.add (continuous_id.mul continuous_const)))
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK hU
    (by rintro _ ⟨s,hs,rfl⟩; exact hseg s hs) hf
  let g : P × ℝ → ℝ := fun q => χ q • f q
  have hnear : ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (0:ℝ) 1,
      g (q.1,a+s*(q.2-a)) = f (q.1,a+s*(q.2-a)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : Continuous (fun z : (P × ℝ) × ℝ => (z.1.1,a+z.2*(z.1.2-a))) :=
      (continuous_fst.fst).prodMk
        (continuous_const.add (continuous_snd.mul (continuous_fst.snd.sub continuous_const)))
    have hk : (p.1,a+s*(p.2-a)) ∈ K := ⟨s,hs,rfl⟩
    exact (hc.continuousAt (x := (p,s))).eventually (he.filter_mono (nhds_le_nhdsSet hk))
  apply (contDiff_parameter_segment_integral hg a).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ segment ℝ a q.2 := by simpa only [segment_eq_uIcc] using hx
  rw [segment_eq_image' ℝ a q.2] at hx'
  obtain ⟨s,hs,rfl⟩ := hx'
  exact (hq s hs).symm

theorem contDiffOn_parameter_segment_integral {f : P × ℝ → ℝ} {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) (a : ℝ) (ha : a ∈ I)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) (V ×ˢ I) := by
  intro p hp
  apply (contDiffAt_parameter_segment_integral (hV.prod hI) hf a p ?_).contDiffWithinAt
  intro s hs
  refine ⟨hp.1,?_⟩
  have hm := hc ha hp.2 (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
  convert hm using 1
  simp only [smul_eq_mul]
  ring


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def layerAreaIntegral (ℓ : Plane → ℝ) (a : ℝ) (q : Plane) : ℝ :=
  ∫ s in a..q.1,ℓ (s,q.2)

theorem layerAreaIntegral_smooth {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1)) :
    ContDiffOn ℝ ∞ (layerAreaIntegral ℓ a) (I ×ˢ Ioo (0:ℝ) 1) := by
  have hs : ContDiffOn ℝ ∞ (fun q : Plane => ℓ (q.2,q.1)) (Ioo (0:ℝ) 1 ×ˢ I) :=
    hℓ.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)
  exact (contDiffOn_parameter_segment_integral isOpen_Ioo hI hc a ha hs).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)

theorem layerAreaIntegral_hasDerivAt {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a s T : ℝ} (ha : a∈I) (hs : s∈I) (hT : T∈Ioo (0:ℝ) 1) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1)) :
    HasDerivAt (fun r => layerAreaIntegral ℓ a (r,T)) (ℓ (s,T)) s := by
  have hcs : ContinuousOn (fun r => ℓ (r,T)) I :=
    hℓ.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr,hT⟩)
  have hseg : uIcc a s ⊆ I := by simpa only [segment_eq_uIcc] using hc.segment_subset ha hs
  exact intervalIntegral.integral_hasDerivAt_right
    (hcs.mono hseg).intervalIntegrable (hcs.stronglyMeasurableAtFilter hI s hs)
    (hcs.continuousAt (hI.mem_nhds hs))

theorem layerAreaIntegral_pos {I : Set ℝ} (hc : Convex ℝ I)
    {a b T : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b) (hT : T∈Ioo (0:ℝ) 1)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q) :
    0<layerAreaIntegral ℓ a (b,T) := by
  have hseg : Icc a b ⊆ I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  apply intervalIntegral.integral_pos hab
    (hℓ.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hseg hr,hT⟩))
  · intro s hs
    exact (hpos (s,T) ⟨hseg ⟨hs.1.le,hs.2⟩,hT⟩).le
  · exact ⟨a,⟨le_rfl,hab.le⟩,hpos (a,T) ⟨ha,hT⟩⟩

variable {ι : Type*} [Fintype ι]

def areaLayerCoordinate (ℓ : Plane → ℝ) (a : ℝ) (ρ : ℝ → ℝ) (H : (ι → ℝ) → ℝ)
    (p : Plane × PlanePhase ι) : ℝ :=
  layerAreaIntegral ℓ a p.1+ρ p.1.1*H (planeMoments p.2)

theorem areaLayerCoordinate_data {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a b : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρpos : ∀ s,0≤deriv ρ s) (hρa : ρ a=0) (hρb : ρ b=1)
    {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    {V : Set (ι → ℝ)} (hHp : ∀ p∈V,0≤H p) :
    ContDiffOn ℝ ∞ (areaLayerCoordinate ℓ a ρ H)
      ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→∀ s∈Ioo a b,
      0<deriv (fun r => areaLayerCoordinate ℓ a ρ H ((r,T),v)) s) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→areaLayerCoordinate ℓ a ρ H ((a,T),v)=0) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→H (planeMoments v)<areaLayerCoordinate ℓ a ρ H ((b,T),v)) := by
  have hseg : Icc a b⊆I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  refine ⟨?_,?_,?_,?_⟩
  · exact ((layerAreaIntegral_smooth hI hc ha hℓ).comp contDiff_fst.contDiffOn
      (fun _ hp => ⟨hseg hp.1.1,hp.1.2⟩)).add
      (((hρ.comp (contDiff_fst.comp contDiff_fst)).mul
        (hH.comp (planeMoments_smooth.comp contDiff_snd))).contDiffOn)
  · intro T hT v hv s hs
    have hd := (layerAreaIntegral_hasDerivAt hI hc ha (hseg ⟨hs.1.le,hs.2.le⟩) hT hℓ).add
      (((hρ.differentiable (by simp) s).hasDerivAt).mul_const (H (planeMoments v)))
    change HasDerivAt (fun r => areaLayerCoordinate ℓ a ρ H ((r,T),v)) _ s at hd
    rw [hd.deriv]
    exact add_pos_of_pos_of_nonneg (hpos (s,T) ⟨hseg ⟨hs.1.le,hs.2.le⟩,hT⟩)
      (mul_nonneg (hρpos s) (hHp _ hv))
  · intro T _ v _
    simp only [areaLayerCoordinate,layerAreaIntegral,intervalIntegral.integral_same,hρa,zero_mul,add_zero]
  · intro T hT v _
    simp only [areaLayerCoordinate,hρb,one_mul]
    exact lt_add_of_pos_left _ (layerAreaIntegral_pos hc ha hb hab hT hℓ hpos)


end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoCovectorForm (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η ζ : E →L[ℝ] ℝ) : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let α := η.comp (ContinuousLinearMap.snd ℝ Plane E)
  oneCovectorForm A c ζ + α.smulRight ds - ds.smulRight α

@[simp] theorem twoCovectorForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η ζ : E →L[ℝ] ℝ) (v w : Plane × E) :
    twoCovectorForm A c η ζ v w = A v.2 w.2 + c*(v.1.1*w.1.2-v.1.2*w.1.1) +
      ζ v.2*w.1.2-v.1.2*ζ w.2 + η v.2*w.1.1-v.1.1*η w.2 := by
  simp [twoCovectorForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem twoCovectorForm_skew {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ v w, A v w = -A w v) (c : ℝ) (η ζ : E →L[ℝ] ℝ) (v w : Plane × E) :
    twoCovectorForm A c η ζ v w = -twoCovectorForm A c η ζ w v := by
  simp only [twoCovectorForm_apply]
  rw [hA v.2 w.2]
  ring

theorem twoCovectorForm_isInvertible [FiniteDimensional ℝ E]
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (hskew : ∀ v w, A v w = -A w v) {c : ℝ} (hc : c ≠ 0)
    (η ζ : E →L[ℝ] ℝ) (hcomm : ζ (A.inverse η)=0) :
    (twoCovectorForm A c η ζ).IsInvertible := by
  have hAi : Injective A := by obtain ⟨e,he⟩ := hA; rw [←he]; exact e.injective
  have hself (α : E →L[ℝ] ℝ) : α (A.inverse α)=0 := by
    have hs := hskew (A.inverse α) (A.inverse α)
    rw [hA.self_apply_inverse] at hs
    linarith
  have hother : η (A.inverse ζ)=0 := by
    have hs := hskew (A.inverse η) (A.inverse ζ)
    rw [hA.self_apply_inverse,hA.self_apply_inverse,hcomm,neg_zero] at hs
    exact hs
  let B := twoCovectorForm A c η ζ
  have hBi : Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    have hAz : A v.2 = v.1.1 • η + v.1.2 • ζ := by
      ext w
      have hh := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,0),w)) hv
      simp only [B,twoCovectorForm_apply,mul_zero,sub_zero,add_zero,zero_apply] at hh
      change A v.2 w=v.1.1*η w+v.1.2*ζ w
      linarith
    have hz : v.2=v.1.1 • A.inverse η+v.1.2 • A.inverse ζ := by
      apply hAi
      rw [map_add,map_smul,map_smul,hA.self_apply_inverse,hA.self_apply_inverse,hAz]
    have hη : η v.2=0 := by rw [hz]; simp only [map_add,map_smul,hself,hother,smul_zero,add_zero]
    have hζ : ζ v.2=0 := by rw [hz]; simp only [map_add,map_smul,hcomm,hself,smul_zero,add_zero]
    have ht := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((1,0),0)) hv
    have hs := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,1),0)) hv
    simp only [B,twoCovectorForm_apply,map_zero,mul_zero,mul_one,sub_zero,
      zero_sub,zero_add,add_zero,hη,hζ,zero_apply] at ht hs
    have hs0 : v.1.1=0 := (mul_eq_zero.mp hs).resolve_left hc
    have ht0 : v.1.2=0 := by
      have hh : c*v.1.2=0 := by linarith
      exact (mul_eq_zero.mp hh).resolve_left hc
    have hz0 : v.2=0 := by rw [hz,hs0,ht0,zero_smul,zero_smul,zero_add]
    exact Prod.ext (Prod.ext hs0 ht0) hz0
  obtain ⟨e,_⟩ := oneCovectorForm_isInvertible hA hc (0 : E →L[ℝ] ℝ)
  exact ⟨(B.toLinearMap.linearEquivOfInjective hBi e.toLinearEquiv.finrank_eq).toContinuousLinearEquiv,rfl⟩



def horizontalOneForm (A B : Plane × E → ℝ) (x : Plane × E) :
    (Plane × E) →L[ℝ] ℝ :=
  A x • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E) +
  B x • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)

@[simp] theorem horizontalOneForm_apply (A B : Plane × E → ℝ) (x v : Plane × E) :
    horizontalOneForm A B x v = A x*v.1.1+B x*v.1.2 := by
  simp [horizontalOneForm,smul_eq_mul]

@[fun_prop] theorem horizontalOneForm_smooth {A B : Plane × E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (horizontalOneForm A B) :=
  (hA.smul contDiff_const).add (hB.smul contDiff_const)

theorem horizontalOneForm_fderiv {A B : Plane × E → ℝ} {x : Plane × E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v w : Plane × E) :
    fderiv ℝ (horizontalOneForm A B) x v w =
      fderiv ℝ A x v*w.1.1+fderiv ℝ B x v*w.1.2 := by
  rw [←fderiv_clm_eval ((hA.smul_const _).add (hB.smul_const _))]
  simp only [horizontalOneForm_apply]
  change fderiv ℝ ((fun y => A y*w.1.1)+(fun y => B y*w.1.2)) x v = _
  rw [fderiv_add (hA.mul_const _) (hB.mul_const _),fderiv_mul_const hA,fderiv_mul_const hB]
  simp only [add_apply,smul_apply,smul_eq_mul,mul_comm]

def horizontalCoupling (Ω : E →L[ℝ] E →L[ℝ] ℝ) (A B : Plane × E → ℝ)
    (x : Plane × E) : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
    euclideanExteriorOneForm (horizontalOneForm A B) x

theorem horizontalCoupling_eq {A B : Plane × E → ℝ} {x : Plane × E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) :
    horizontalCoupling Ω A B x =
      twoCovectorForm Ω (fderiv ℝ B x ((1,0),0)-fderiv ℝ A x ((0,1),0))
        ((fderiv ℝ A x).comp (ContinuousLinearMap.inr ℝ Plane E))
        ((fderiv ℝ B x).comp (ContinuousLinearMap.inr ℝ Plane E)) := by
  have decomp (L : (Plane × E) →L[ℝ] ℝ) (v : Plane × E) :
      L v=v.1.1*L ((1,0),0)+v.1.2*L ((0,1),0)+L ((0,0),v.2) := by
    have he : v=v.1.1 • ((1,0),0)+v.1.2 • ((0,1),0)+((0,0),v.2) := by
      ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [horizontalCoupling,add_apply,ContinuousLinearMap.bilinearComp_apply,
    euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,twoCovectorForm_apply,
    horizontalOneForm_fderiv hA hB,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  rw [decomp (fderiv ℝ A x) v,decomp (fderiv ℝ A x) w,
    decomp (fderiv ℝ B x) v,decomp (fderiv ℝ B x) w]
  change Ω v.2 w.2 +
      ((v.1.1*(fderiv ℝ A x) ((1,0),0)+v.1.2*(fderiv ℝ A x) ((0,1),0)+(fderiv ℝ A x) ((0,0),v.2))*w.1.1+
       (v.1.1*(fderiv ℝ B x) ((1,0),0)+v.1.2*(fderiv ℝ B x) ((0,1),0)+(fderiv ℝ B x) ((0,0),v.2))*w.1.2-
       ((w.1.1*(fderiv ℝ A x) ((1,0),0)+w.1.2*(fderiv ℝ A x) ((0,1),0)+(fderiv ℝ A x) ((0,0),w.2))*v.1.1+
        (w.1.1*(fderiv ℝ B x) ((1,0),0)+w.1.2*(fderiv ℝ B x) ((0,1),0)+(fderiv ℝ B x) ((0,0),w.2))*v.1.2)) = Ω v.2 w.2 +
      ((fderiv ℝ B x) ((1,0),0)-(fderiv ℝ A x) ((0,1),0))*(v.1.1*w.1.2-v.1.2*w.1.1)+
      (fderiv ℝ B x) ((0,0),v.2)*w.1.2-v.1.2*(fderiv ℝ B x) ((0,0),w.2)+
      (fderiv ℝ A x) ((0,0),v.2)*w.1.1-v.1.1*(fderiv ℝ A x) ((0,0),w.2)
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
