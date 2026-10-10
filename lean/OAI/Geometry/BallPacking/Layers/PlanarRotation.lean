import Mathlib
import OAI.Geometry.BallPacking.Layers.ParametricNestedDisks

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

def planeRotate (θ : ℝ) (v : Plane) : Plane :=
  (Real.cos θ*v.1-Real.sin θ*v.2,Real.sin θ*v.1+Real.cos θ*v.2)

@[fun_prop] theorem planeRotate_smooth : ContDiff ℝ ∞ (fun p : ℝ × Plane => planeRotate p.1 p.2) := by
  unfold planeRotate
  fun_prop

@[simp] theorem planeRotate_zero (v : Plane) : planeRotate 0 v = v := by
  ext <;> simp [planeRotate]

@[simp] theorem radiusSq_planeRotate (θ : ℝ) (v : Plane) :
    radiusSq (planeRotate θ v) = radiusSq v := by
  unfold radiusSq planeRotate
  nlinarith only [Real.sin_sq_add_cos_sq θ]

@[simp] theorem radialArea_planeRotate (θ : ℝ) (v : Plane) :
    radialArea (planeRotate θ v) = radialArea v := by
  simp [radialArea]

theorem planeRotate_hasDerivAt {θ : ℝ → ℝ} {t a : ℝ} (hθ : HasDerivAt θ a t) (v : Plane) :
    HasDerivAt (fun s => planeRotate (θ s) v)
      (a • (-(planeRotate (θ t) v).2,(planeRotate (θ t) v).1)) t := by
  have h1 := ((Real.hasDerivAt_cos (θ t)).comp t hθ).mul_const v.1
  have h2 := ((Real.hasDerivAt_sin (θ t)).comp t hθ).mul_const v.2
  have h3 := ((Real.hasDerivAt_sin (θ t)).comp t hθ).mul_const v.1
  have h4 := ((Real.hasDerivAt_cos (θ t)).comp t hθ).mul_const v.2
  apply ((h1.sub h2).prodMk (h3.add h4)).congr_deriv
  ext <;> dsimp [planeRotate] <;> ring

@[fun_prop] theorem radialArea_smooth : ContDiff ℝ ∞ radialArea :=
  contDiff_const.mul radiusSq_smooth

theorem radialArea_hasFDerivAt (x : Plane) :
    HasFDerivAt radialArea
      (Real.pi • ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have h₁ : HasFDerivAt (fun p : Plane => p.1^2)
      ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2
  have h₂ : HasFDerivAt (fun p : Plane => p.2^2)
      ((2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2
  exact (h₁.add h₂).const_mul Real.pi

@[simp] theorem radialArea_fderiv (x v : Plane) :
    fderiv ℝ radialArea x v = 2*Real.pi*(x.1*v.1+x.2*v.2) := by
  rw [(radialArea_hasFDerivAt x).fderiv]
  change Real.pi * (2*x.1*v.1+2*x.2*v.2) = _
  ring


end

section
open scoped ContDiff Topology BigOperators
open Set Function MeasureTheory

theorem exists_hamiltonian_thin_grid {m : ℕ} (h : Fin m → ℝ)
    (hh : ∀ i, 0 < h i) (hmono : StrictMono h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R : ℝ) (Ψ : HamiltonianDiskIsotopyFamily ℝ R),
      ∀ i x, radialArea x ≤ h i →
        0 < (Ψ.isotopy.map 0 1 x).1 ∧ (Ψ.isotopy.map 0 1 x).1 < h i+δ/2 ∧
        (Ψ.isotopy.map 0 1 x).2 ∈ Ioo 0 1 := by
  obtain ⟨L,w,c,hL,hw,hwmono,hareaL,hnestL,hplace⟩ :=
    exists_thin_rectangle_placement h hh hmono hδ
  let Y : Set ℝ := {0}
  let V (_ : ℝ) (i : Fin m) : Set ℝ := Ioo 0 (h i+δ/2)
  have hV (i : Fin m) : IsOpen {p : ℝ × ℝ | p.2 ∈ V p.1 i} :=
    isOpen_Ioo.preimage continuous_snd
  obtain ⟨q,k,hq,hq1,hk,hsquare,harea,hmargin⟩ :=
    exists_exact_area_rounded_margins (isCompact_singleton (x := (0:ℝ)))
      (fun _ : ℝ => c) continuous_const L w hwmono V hV
      (fun _ _ => ⟨hplace,hnestL⟩)
  let s : ℝ := 4/squeezedArea k
  have hs : 0 < s := div_pos (by norm_num) harea
  let C (i : Fin m) : Plane := (c i+L i/2,1/2)
  let a (i : Fin m) := s*L i/2
  let b (i : Fin m) := w i/2
  have ha i : 0 < a i := div_pos (mul_pos hs (hL i)) (by norm_num)
  have hb i : 0 < b i := div_pos (hw i).1 (by norm_num)
  have hmar := hmargin 0 (mem_singleton (0:ℝ))
  have hnest ⦃i j : Fin m⦄ (hij : i < j) :
      roundedBox k (C i) (a i) (b i) ⊆ interior (roundedBox k (C j) (a j) (b j)) := by
    apply roundedBox_nested_of_margins (ha i) (hb i) (ha j) (hb j) hsquare
    all_goals
      have hn := hmar.2.2 hij
      dsimp only [C,a,b]
      nlinarith only [hn.1,hn.2.1,hn.2.2]
  have hbound (i : Fin m) {x : Plane} (hx : x ∈ roundedBox k (C i) (a i) (b i)) :
      0 < x.1 ∧ x.1 < h i+δ/2 ∧ x.2 ∈ Ioo 0 1 := by
    obtain ⟨z,_,rfl⟩ := hx
    have hz := roundedMap_mem_openBox (ha i) (hb i) k (C i) z
    have he := hmar.2.1 i
    change (0 < c i+L i/2-s*L i/2 ∧ c i+L i/2-s*L i/2 < h i+δ/2) ∧
      (0 < c i+L i/2+s*L i/2 ∧ c i+L i/2+s*L i/2 < h i+δ/2) at he
    change (c i+L i/2-s*L i/2 < _ ∧ _ < c i+L i/2+s*L i/2) ∧
      (1/2-w i/2 < _ ∧ _ < 1/2+w i/2) at hz
    exact ⟨he.1.1.trans hz.1.1,hz.1.2.trans he.2.2,
      by linarith [hz.2.1,(hw i).2],by linarith [hz.2.2,(hw i).2]⟩
  have hvol (i : Fin m) : volume (roundedBox k (C i) (a i) (b i)) = ENNReal.ofReal (h i) := by
    rw [roundedBox_volume_eq (ha i).le (hb i).le]
    congr 1
    calc
      a i*b i*squeezedArea k = L i*w i := by
        dsimp [a,b,s]
        field_simp [harea.ne']
        ring
      _ = h i := hareaL i
  let r i := areaRadius (h i)
  have hr i : 0 < r i := areaRadius_pos (hh i)
  have hrmono : StrictMono r := fun i j hij =>
    areaRadius_strictMono (hh i).le (hh j).le (hmono hij)
  let f (i : Fin m) (p : ℝ × Plane) := normalizedRoundedMap k (C i) (a i) (b i) (r i) p.2
  have himage (i : Fin m) (y : ℝ) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) = roundedBox k (C i) (a i) (b i) :=
    normalizedRoundedMap_image (hr i) k (C i) (a i) (b i)
  let K := ⋃ i, roundedBox k (C i) (a i) (b i)
  have hK : IsCompact K := isCompact_iUnion (fun i => roundedBox_compact k (C i) (a i) (b i))
  obtain ⟨M,hM⟩ := (hK.image radialArea_smooth.continuous).bddAbove
  let T := max (M+1) (1+∑ i, h i)
  have hT : 0 < T := by
    have hs : 0 ≤ ∑ i, h i := Finset.sum_nonneg (fun i _ => (hh i).le)
    have hl := le_max_right (M+1) (1+∑ i, h i)
    dsimp [T]; linarith
  have hiT (i : Fin m) : h i < T := by
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hh j).le) (Finset.mem_univ i)
    have hl := le_max_right (M+1) (1+∑ i, h i)
    dsimp [T]; linarith
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_plane_disk_germs
    (Y := Y) (A := univ) isCompact_singleton (convex_singleton 0) isOpen_univ
    (subset_univ Y) 0 (mem_singleton 0) r hr hrmono f
    (fun i => ((normalizedRoundedMap_smooth k (C i) (a i) (b i) (r i)).comp contDiff_snd).contDiffOn)
    (fun i _ _ => normalizedRoundedMap_injective hk (ha i) (hb i) (hr i) (C i))
    (fun i _ _ x => normalizedRoundedMap_det_pos hk (ha i) (hb i) (hr i) (C i) x)
    (by intro i j hij y _; rw [himage,himage]; exact hnest hij)
    (areaRadius T) (areaRadius_pos hT)
    (fun i => areaRadius_strictMono (hh i).le hT.le (hiT i))
    (by
      intro i y _ x hx
      rw [himage] at hx
      rw [mem_roundDisk_areaRadius hT.le]
      have hm : radialArea x ≤ M := hM (mem_image_of_mem radialArea (mem_iUnion.mpr ⟨i,hx⟩))
      have ht := le_max_left (M+1) (1+∑ i, h i)
      dsimp [T]; linarith)
    (by intro i y _; rw [himage,hvol,volume_closedRoundDisk_areaRadius (hh i).le])
  refine ⟨areaRadius T,Ψ,?_⟩
  intro i x hx
  apply hbound i
  rw [←himage i 0,←hΨ i 0 (mem_singleton 0)]
  exact mem_image_of_mem _ ((mem_closedRoundDisk_areaRadius (hh i).le x).mpr hx)

theorem exists_thin_planar_embedding {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ q : Plane ≃ₜ Plane, ContDiff ℝ ∞ q ∧ ContDiff ℝ ∞ q.symm ∧
      (∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w) ∧
      ∀ x, radialArea x ≤ A →
        0 < (q x).1 ∧ (q x).1 < radialArea x+δ ∧ (q x).2 ∈ Ioo 0 1 := by
  obtain ⟨m,h,hmono,hh,hgrid⟩ := Comparison.exists_positive_area_grid hA
    (show 0 < δ/2 by positivity)
  obtain ⟨R,Ψ,hΨ⟩ := exists_hamiltonian_thin_grid h hh hmono hδ
  refine ⟨Ψ.isotopy.map 0 1,?_,?_,Ψ.symplectic 0 1,?_⟩
  · exact Ψ.isotopy.smooth.comp ((contDiff_const (c := ((0,1) : ℝ × ℝ))).prodMk contDiff_id)
  · exact Ψ.isotopy.inverse_smooth.comp ((contDiff_const (c := ((0,1) : ℝ × ℝ))).prodMk contDiff_id)
  · intro x hx
    have hx0 : 0 ≤ radialArea x := mul_nonneg Real.pi_pos.le (by
      dsimp [radiusSq]; positivity)
    obtain ⟨i,hi,hiδ⟩ := hgrid (radialArea x) ⟨hx0,hx⟩
    have hb := hΨ i x hi
    exact ⟨hb.1,by linarith [hb.2.1],hb.2.2⟩


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def productForm (A : E →L[ℝ] E →L[ℝ] ℝ) :
    (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  planarArea.bilinearComp (ContinuousLinearMap.fst ℝ Plane E) (ContinuousLinearMap.fst ℝ Plane E) +
    A.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E)

@[simp] theorem productForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (v w : Plane × E) :
    productForm A v w = planarArea v.1 w.1 + A v.2 w.2 := by simp [productForm]

def oneCovectorForm (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (η : E →L[ℝ] ℝ) :
    (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let α := η.comp (ContinuousLinearMap.snd ℝ Plane E)
  A.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
    c • (ds.smulRight dt - dt.smulRight ds) + α.smulRight dt - dt.smulRight α

@[simp] theorem oneCovectorForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η : E →L[ℝ] ℝ) (v w : Plane × E) :
    oneCovectorForm A c η v w = A v.2 w.2 + c*(v.1.1*w.1.2-v.1.2*w.1.1) +
      η v.2*w.1.2-v.1.2*η w.2 := by
  simp [oneCovectorForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem oneCovectorForm_skew {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ v w, A v w = -A w v) (c : ℝ) (η : E →L[ℝ] ℝ) (v w : Plane × E) :
    oneCovectorForm A c η v w = -oneCovectorForm A c η w v := by
  simp only [oneCovectorForm_apply]
  rw [hA v.2 w.2]
  ring

theorem oneCovectorForm_isInvertible [FiniteDimensional ℝ E] {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) {c : ℝ} (hc : c ≠ 0) (η : E →L[ℝ] ℝ) :
    (oneCovectorForm A c η).IsInvertible := by
  let B := oneCovectorForm A c η
  have hAi : Injective A := by obtain ⟨e,he⟩ := hA; rw [←he]; exact e.injective
  have hBi : Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    have ht := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((1,0),0)) hv
    have ht0 : v.1.2 = 0 := by
      simp only [B,oneCovectorForm_apply,map_zero,mul_zero,sub_zero,mul_one,zero_add,
        zero_sub,zero_apply] at ht
      have he : c*v.1.2 = 0 := by linarith
      exact (mul_eq_zero.mp he).resolve_left hc
    have hf : A v.2 = 0 := by
      apply ContinuousLinearMap.ext
      intro z
      have hz := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,0),z)) hv
      simpa [B,ht0] using hz
    have hf0 : v.2 = 0 := hAi (hf.trans A.map_zero.symm)
    have hs := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,1),0)) hv
    have hs0 : v.1.1 = 0 := by
      simp only [B,oneCovectorForm_apply,hf0,ht0,map_zero,mul_zero,mul_one,sub_zero,
        zero_add,add_zero,zero_apply] at hs
      exact (mul_eq_zero.mp hs).resolve_left hc
    exact Prod.ext (Prod.ext hs0 ht0) hf0
  have hBs : Surjective B := by
    intro β
    let t : ℝ := -β ((1,0),0)/c
    let α : E →L[ℝ] ℝ := β.comp (ContinuousLinearMap.inr ℝ Plane E) + t • η
    let z := A.inverse α
    let s := (β ((0,1),0)-η z)/c
    refine ⟨((s,t),z),?_⟩
    apply ContinuousLinearMap.ext
    intro v
    have hz : A z v.2 = β ((0,0),v.2)+t*η v.2 := by
      change A (A.inverse α) v.2 = _
      rw [hA.self_apply_inverse]
      rfl
    have ht : c*t = -β ((1,0),0) := by dsimp [t]; field_simp
    have hs : c*s = β ((0,1),0)-η z := by dsimp [s]; field_simp
    have hβ : β v = v.1.1*β ((1,0),0)+v.1.2*β ((0,1),0)+β ((0,0),v.2) := by
      conv_lhs => rw [show v = v.1.1 • (((1,0),0) : Plane × E) +
          v.1.2 • (((0,1),0) : Plane × E) + ((0,0),v.2) by ext <;> simp]
      simp only [map_add,map_smul,smul_eq_mul]
    change oneCovectorForm A c η ((s,t),z) v = _
    rw [oneCovectorForm_apply,hz,hβ]
    linear_combination v.1.2*hs-v.1.1*ht
  exact ⟨(LinearEquiv.ofBijective B.toLinearMap ⟨hBi,hBs⟩).toContinuousLinearEquiv,rfl⟩


end

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def planarProduct (q : Plane ≃ₜ Plane) : (Plane × E) ≃ₜ (Plane × E) :=
  q.prodCongr (Homeomorph.refl E)

@[fun_prop] theorem planarProduct_smooth {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (planarProduct (E := E) q) :=
  (hq.comp contDiff_fst).prodMk contDiff_snd

theorem planarProduct_fderiv {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q)
    (p v : Plane × E) : fderiv ℝ (planarProduct q) p v = (fderiv ℝ q p.1 v.1,v.2) := by
  have hd := (((hq.differentiable (by simp) p.1).hasFDerivAt).comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (planarProduct q) _ p at hd
  rw [hd.fderiv]
  rfl

theorem planarProduct_pullback {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q)
    (hqs : ∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (p v w : Plane × E) :
    productForm B (fderiv ℝ (planarProduct q) p v) (fderiv ℝ (planarProduct q) p w) =
      productForm B v w := by
  rw [planarProduct_fderiv hq,planarProduct_fderiv hq]
  simp only [productForm_apply]
  rw [hqs]


end

open scoped ContDiff Topology
open Set Function
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem monotone_strip_inverse {f : Q × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {U : Set Q} (hU : IsOpen U) {a b : ℝ} (hab : a < b) {h : Q → ℝ}
    (hderiv : ∀ q ∈ U, ∀ s ∈ Ioo a b, 0 < deriv (fun r => f (q,r)) s)
    (hlo : ∀ q ∈ U, f (q,a) = 0) (hhi : ∀ q ∈ U, h q < f (q,b)) :
    ∃ (W : Set (Q × ℝ)) (g : Q × ℝ → ℝ), IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = (fun p : Q × ℝ => (p.1,f p)) '' (U ×ˢ Ioo a b) ∧
      (∀ q ∈ U, ∀ x, 0 < x → x < h q → (q,x) ∈ W) ∧
      (∀ q ∈ U, ∀ s ∈ Ioo a b, g (q,f (q,s)) = s) ∧
      (∀ p ∈ W, p.1 ∈ U ∧ g p ∈ Ioo a b ∧ f (p.1,g p) = p.2) := by
  have hc (q : Q) : Continuous (fun s => f (q,s)) :=
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hm (q : Q) (hq : q ∈ U) : StrictMonoOn (fun s => f (q,s)) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (hc q).continuousOn
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
  obtain ⟨W,g,hWo,hgs,hWe,hleft,hright⟩ := parametric_inverse_on f hf
    (U ×ˢ Ioo a b) (hU.prod isOpen_Ioo) hinj hiv
  refine ⟨W,g,hWo,hgs,hWe,?_,?_,?_⟩
  · intro q hq x hx0 hxh
    have hh : x ∈ Ioo (f (q,a)) (f (q,b)) := ⟨by rwa [hlo q hq],hxh.trans (hhi q hq)⟩
    obtain ⟨s,hs,hse⟩ := intermediate_value_Ioo hab.le (hc q).continuousOn hh
    rw [hWe]
    exact ⟨(q,s),⟨hq,hs⟩,Prod.ext rfl hse⟩
  · intro q hq s hs
    exact (hleft (q,s) ⟨hq,hs⟩).2
  · intro p hp
    exact ⟨(hright p hp).1.1,(hright p hp).1.2,(hright p hp).2⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
