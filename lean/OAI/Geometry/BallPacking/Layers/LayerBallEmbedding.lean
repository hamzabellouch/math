import Mathlib
import OAI.Geometry.BallPacking.Layers.SmoothFormTransport

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def splitCapacityBall (r : ℝ) : Set (Plane × PlanePhase ι) :=
  {z | radialArea z.1 + ∑ i, planeMoments z.2 i ≤ r}

private theorem inverse_layer_product_pullback {F : (ι → ℝ) → ℝ}
    {g : Plane × PlanePhase ι → Plane × PlanePhase ι}
    {f₀ : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f₀)
    {U W : Set (Plane × PlanePhase ι)} (hU : IsOpen U) (hW : IsOpen W)
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
    (layerChart_smooth hF hf).contDiffOn hg hr (layerForm F f₀) (productForm phaseArea)
    (fun x _ u t => layerChart_pullback hF hf x u t) (planarProduct_smooth (E := PlanePhase ι) (q := q) hqs)
    (fun x u t => planarProduct_pullback (E := PlanePhase ι) (q := q) hqs hqform (phaseArea (ι := ι)) x u t) hz v w

theorem exists_ball_in_layer {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
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
  obtain ⟨W,g,hW,hg,himage,ha,hl,hr⟩ := layerChart_inverse hF hf hV hab H hderiv hlo hhi
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
    inverse_chart_isEmbedding (layerChart_smooth hF hf).continuous.continuousOn
      hg.continuousOn himage.symm hl hr
  let j : N → W := fun z => ⟨Q z,z.property⟩
  have hje : Topology.IsEmbedding j :=
    (Q.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict W (fun z => z.property)
  refine ⟨N,φ,hN,hball,hsφ,hge.comp hje,?_,?_⟩
  · intro z hz
    exact (hr (Q z) hz).1
  · intro z hz v w
    exact inverse_layer_product_pullback hF hf hU hW hg hr hqs hqform hz v w


end

section
open scoped ContDiff Topology BigOperators
open Set Function

def complexSplitPhaseLinear (m : ℕ) : Ambient (m+1) ≃ₗ[ℝ] Plane × PlanePhase (Fin m) where
  toFun z := (((z 0).re,(z 0).im),fun j => ((z j.succ).re,(z j.succ).im))
  invFun p := Fin.cons (⟨p.1.1,p.1.2⟩ : ℂ) (fun j => (⟨(p.2 j).1,(p.2 j).2⟩ : ℂ))
  left_inv z := by funext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    ext <;> simp [Pi.smul_apply]

def complexSplitPhase (m : ℕ) : Ambient (m+1) ≃L[ℝ] Plane × PlanePhase (Fin m) :=
  (complexSplitPhaseLinear m).toContinuousLinearEquiv

@[simp] theorem complexSplitPhase_apply (m : ℕ) (z : Ambient (m+1)) :
    complexSplitPhase m z=(((z 0).re,(z 0).im),fun j => ((z j.succ).re,(z j.succ).im)) := rfl

theorem complexSplitPhase_capacity (m : ℕ) (z : Ambient (m+1)) :
    radialArea (complexSplitPhase m z).1 + ∑ j,planeMoments (complexSplitPhase m z).2 j = capacity z := by
  simp only [complexSplitPhase_apply,radialArea,radiusSq,planeMoments,capacity,Fin.sum_univ_succ,
    Complex.normSq_apply,Finset.mul_sum,mul_add,pow_two]

theorem complexSplitPhase_form (m : ℕ) (v w : Ambient (m+1)) :
    productForm phaseArea (complexSplitPhase m v) (complexSplitPhase m w)=standardForm v w := by
  simp only [productForm_apply,phaseArea_apply,complexSplitPhase_apply,standardForm,Fin.sum_univ_succ]
  rfl

@[simp] theorem complexSplitPhase_preimage_ball (m : ℕ) (r : ℝ) :
    complexSplitPhase m ⁻¹' splitCapacityBall r=closedBall (m+1) r := by
  ext z
  change radialArea (complexSplitPhase m z).1+∑ j,planeMoments (complexSplitPhase m z).2 j ≤ r ↔ capacity z ≤ r
  rw [complexSplitPhase_capacity]

theorem complex_ball_of_split_embedding {m : ℕ} {r : ℝ}
    {Ω : Plane × PlanePhase (Fin m) → (Plane × PlanePhase (Fin m)) →L[ℝ]
      (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ}
    {N : Set (Plane × PlanePhase (Fin m))} {φ : Plane × PlanePhase (Fin m) → Plane × PlanePhase (Fin m)}
    (hN : IsOpen N) (hball : splitCapacityBall r ⊆ N) (hs : ContDiffOn ℝ ∞ φ N)
    (he : Topology.IsEmbedding (fun z : N => φ z))
    (hform : ∀ z ∈ N,∀ v w,Ω (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w)=productForm phaseArea v w) :
    ∃ U : Set (Ambient (m+1)),IsOpen U ∧ closedBall (m+1) r ⊆ U ∧
      ContDiffOn ℝ ∞ (φ ∘ complexSplitPhase m) U ∧
      Topology.IsEmbedding (fun z : U => φ (complexSplitPhase m z)) ∧
      (∀ z ∈ U,φ (complexSplitPhase m z)∈φ '' N) ∧
      ∀ z ∈ U,∀ v w,Ω (φ (complexSplitPhase m z))
        (fderiv ℝ (φ ∘ complexSplitPhase m) z v) (fderiv ℝ (φ ∘ complexSplitPhase m) z w)=standardForm v w := by
  let e := complexSplitPhase m
  let U := e ⁻¹' N
  have hU : IsOpen U := hN.preimage e.continuous
  have hm : MapsTo e U N := fun _ hz => hz
  let j : U → N := fun z => ⟨e z,z.property⟩
  have hj : Topology.IsEmbedding j :=
    (e.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict N (fun z => z.property)
  refine ⟨U,hU,?_,hs.comp e.contDiff.contDiffOn hm,he.comp hj,?_,?_⟩
  · intro z hz
    apply hball
    have hz' : z∈e ⁻¹' splitCapacityBall r := by
      simpa only [e,complexSplitPhase_preimage_ball] using hz
    exact hz'
  · intro z hz
    exact mem_image_of_mem φ hz
  · intro z hz v w
    have hd := fderiv_comp z
      ((hs.contDiffAt (hN.mem_nhds hz)).differentiableAt (by simp)) e.differentiableAt
    rw [hd,e.fderiv]
    change Ω (φ (e z)) (fderiv ℝ φ (e z) (e v)) (fderiv ℝ φ (e z) (e w))=standardForm v w
    rw [hform (e z) hz,complexSplitPhase_form]


end

section
open scoped ContDiff Topology
open Set Function
variable {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem parametric_inverse_on_local (f : Q × E → E)
    (D : Set (Q × E)) (hD : IsOpen D) (hf : ContDiffOn ℝ ∞ f D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible) :
    ∃ (U : Set (Q × E)) (g : Q × E → E), IsOpen U ∧ ContDiffOn ℝ ∞ g U ∧
      U = (fun p => (p.1,f p)) '' D ∧
      (∀ p ∈ D, (p.1,f p) ∈ U ∧ g (p.1,f p) = p.2) ∧
      (∀ p ∈ U, (p.1,g p) ∈ D ∧ f (p.1,g p) = p.2) := by
  let F : Q × E → Q × E := fun p => (p.1,f p)
  have hF : ContDiffOn ℝ ∞ F D := contDiffOn_fst.prodMk hf
  have hFi : InjOn F D := by
    rintro ⟨t,x⟩ hp ⟨s,y⟩ hq he
    have ht : t = s := congrArg (fun z : Q × E => z.1) he
    cases ht
    have hx : f (t,x) = f (t,y) := congrArg (fun z : Q × E => z.2) he
    exact Prod.ext rfl (hinj t hp hq hx)
  have hFd (p : Q × E) (hp : p∈D) : fderiv ℝ F p =
      (ContinuousLinearMap.fst ℝ Q E).prod (fderiv ℝ f p) := by
    exact (hasFDerivAt_fst.prodMk ((hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hFiv (p : Q × E) (hp : p ∈ D) : (fderiv ℝ F p).IsInvertible := by
    rw [hFd p hp]
    apply clockGraph_linear_invertible
    have hd : fderiv ℝ (fun x => f (p.1,x)) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Q E) := by
      exact (((hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
    rw [← hd]
    exact hi p hp
  obtain ⟨hU,hg,hleft,hright⟩ := smooth_inverse_on hD hF hFi hFiv
  let g : Q × E → E := fun p => (invFunOn F D p).2
  refine ⟨F '' D,g,hU,hg.snd,rfl,?_,?_⟩
  · intro p hp
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    exact congrArg Prod.snd (hleft p hp)
  · intro p hp
    have he := hright p hp
    change ((invFunOn F D p).1,f (invFunOn F D p)) = p at he
    have hfirst := congrArg (fun z : Q × E => z.1) he
    have hmem := invFunOn_mem hp
    have hid : (p.1,g p) = invFunOn F D p := Prod.ext hfirst.symm rfl
    rw [hid]
    exact ⟨hmem,congrArg (fun z : Q × E => z.2) he⟩


end

section
open scoped ContDiff Topology
open Set Function
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem monotone_strip_inverse_local {f : Q × ℝ → ℝ}
    {U : Set Q} (hU : IsOpen U) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Icc a b)) {h : Q → ℝ}
    (hderiv : ∀ q ∈ U, ∀ s ∈ Ioo a b, 0 < deriv (fun r => f (q,r)) s)
    (hlo : ∀ q ∈ U, f (q,a) = 0) (hhi : ∀ q ∈ U, h q < f (q,b)) :
    ∃ (W : Set (Q × ℝ)) (g : Q × ℝ → ℝ), IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = (fun p : Q × ℝ => (p.1,f p)) '' (U ×ˢ Ioo a b) ∧
      (∀ q ∈ U, ∀ x, 0 < x → x < h q → (q,x) ∈ W) ∧
      (∀ q ∈ U, ∀ s ∈ Ioo a b, g (q,f (q,s)) = s) ∧
      (∀ p ∈ W, p.1 ∈ U ∧ g p ∈ Ioo a b ∧ f (p.1,g p) = p.2) := by
  have hc (q : Q) (hq : q∈U) : ContinuousOn (fun s => f (q,s)) (Icc a b) :=
    hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => ⟨hq,hs⟩)
  have hm (q : Q) (hq : q ∈ U) : StrictMonoOn (fun s => f (q,s)) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (hc q hq)
    simpa only [interior_Icc] using hderiv q hq
  have hinj (q : Q) : InjOn (fun s => f (q,s)) {s | (q,s) ∈ U ×ˢ Ioo a b} := by
    intro s hs t ht he
    exact (hm q hs.1).injOn ⟨hs.2.1.le,hs.2.2.le⟩ ⟨ht.2.1.le,ht.2.2.le⟩ he
  have hiv (p : Q × ℝ) (hp : p ∈ U ×ˢ Ioo a b) :
      (fderiv ℝ (fun s => f (p.1,s)) p.2).IsInvertible := by
    let c := deriv (fun s => f (p.1,s)) p.2
    have hc0 : c ≠ 0 := ne_of_gt (hderiv p.1 hp.1 p.2 hp.2)
    let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ c hc0).toContinuousLinearEquiv
    refine ⟨e,?_⟩
    ext
    simp [e,c]
  obtain ⟨W,g,hWo,hgs,hWe,hleft,hright⟩ := parametric_inverse_on_local f
    (U ×ˢ Ioo a b) (hU.prod isOpen_Ioo) (hf.mono (prod_mono_right Ioo_subset_Icc_self)) hinj hiv
  refine ⟨W,g,hWo,hgs,hWe,?_,?_,?_⟩
  · intro q hq x hx0 hxh
    have hh : x ∈ Ioo (f (q,a)) (f (q,b)) := ⟨by rwa [hlo q hq],hxh.trans (hhi q hq)⟩
    obtain ⟨s,hs,hse⟩ := intermediate_value_Ioo hab.le (hc q hq) hh
    rw [hWe]
    exact ⟨(q,s),⟨hq,hs⟩,Prod.ext rfl hse⟩
  · intro q hq s hs
    exact (hleft (q,s) ⟨hq,hs⟩).2
  · intro p hp
    exact ⟨(hright p hp).1.1,(hright p hp).1.2,(hright p hp).2⟩


end

open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stripChart_inverse_local {f : Plane × E → ℝ}
    {V : Set E} (hV : IsOpen V) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V)) (H : E → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, H v < f ((b,T),v)) :
    ∃ (W : Set (Plane × E)) (g : Plane × E → Plane × E),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = stripChart f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → p.2 ∈ V → 0 < p.1.1 → p.1.1 < H p.2 → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V, g (stripChart f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V ∧ stripChart f (g p) = p) := by
  let e : (Plane × E) ≃L[ℝ] ((ℝ × E) × ℝ) := layerOrder
  let f' : (ℝ × E) × ℝ → ℝ := f ∘ e.symm
  have hf' : ContDiffOn ℝ ∞ f' ((Ioo (0:ℝ) 1 ×ˢ V) ×ˢ Icc a b) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ hp => ⟨⟨hp.2,hp.1.1⟩,hp.1.2⟩)
  obtain ⟨W,g,hWo,hgs,hWe,havailable,hleft,hright⟩ := monotone_strip_inverse_local
    (isOpen_Ioo.prod hV) hab hf' (h := fun q : ℝ × E => H q.2)
    (fun q hq s hs => hderiv q.1 hq.1 q.2 hq.2 s hs)
    (fun q hq => hlo q.1 hq.1 q.2 hq.2)
    (fun q hq => hhi q.1 hq.1 q.2 hq.2)
  let G : Plane × E → Plane × E := fun p => ((g (e p),p.1.2),p.2)
  refine ⟨e ⁻¹' W,G,hWo.preimage e.continuous,?_,?_,?_,?_,?_⟩
  · have hg : ContDiffOn ℝ ∞ (fun p => g (e p)) (e ⁻¹' W) :=
      hgs.comp e.contDiff.contDiffOn (fun _ hp => hp)
    exact (hg.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn
  · ext p
    constructor
    · intro hp
      obtain ⟨q,hq,hqe⟩ := by simpa only [hWe] using hp
      refine ⟨e.symm q,⟨⟨hq.2,hq.1.1⟩,hq.1.2⟩,?_⟩
      apply e.injective
      change (q.1,f' q) = e p
      exact hqe
    · rintro ⟨q,hq,rfl⟩
      change e (stripChart f q) ∈ W
      rw [hWe]
      exact ⟨e q,⟨⟨hq.1.2,hq.2⟩,hq.1.1⟩,rfl⟩
  · intro p hpT hpV hp0 hpH
    exact havailable (p.1.2,p.2) ⟨hpT,hpV⟩ p.1.1 hp0 hpH
  · intro p hp
    have hh := hleft (p.1.2,p.2) ⟨hp.1.2,hp.2⟩ p.1.1 hp.1.1
    change ((g ((p.1.2,p.2),f p),p.1.2),p.2) = p
    change g ((p.1.2,p.2),f p) = p.1.1 at hh
    rw [hh]
  · intro p hp
    have hh := hright (e p) hp
    refine ⟨⟨⟨hh.2.1,hh.1.1⟩,hh.1.2⟩,?_⟩
    change ((f ((g (e p),p.1.2),p.2),p.1.2),p.2) = p
    have he : f ((g (e p),p.1.2),p.2) = p.1.1 := hh.2.2
    rw [he]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
