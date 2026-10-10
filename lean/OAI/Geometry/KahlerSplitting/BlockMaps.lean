import OAI.Geometry.KahlerSplitting.DiskAxes

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsBlockBox (S : HolomorphicSplitting X r s) (U : Set (E × F)) (f : E × F → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E × F) (model n) f U ∧ ∀ z ∈ U,
    (∀ v : E, S.projection (f z) (mfderiv 𝓘(ℂ,E × F) (model n) f z (v,0)) =
      mfderiv 𝓘(ℂ,E × F) (model n) f z (v,0)) ∧
    (∀ w : F, S.projection (f z) (mfderiv 𝓘(ℂ,E × F) (model n) f z (0,w)) = 0)

lemma IsBlockBox.mono {U V : Set (E × F)} {f : E × F → X.Carrier}
    (hf : IsBlockBox S U f) (hV : V ⊆ U) : IsBlockBox S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma SplittingChart.block_coordinates (e : SplittingChart S) {U : Set (E × F)}
    (hU : IsOpen U) {f : E × F → X.Carrier} (hf : IsBlockBox S U f)
    (he : MapsTo f U e.chart.source) :
    DifferentiableOn ℂ (e.chart ∘ f) U ∧ ∀ z ∈ U,
      (∀ v : E, (fderiv ℂ (e.chart ∘ f) z (v,0)).2=0) ∧
      (∀ w : F, (fderiv ℂ (e.chart ∘ f) z (0,w)).1=0) := by
  refine ⟨mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf.1 he),?_⟩
  intro z hz
  have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
    (hf.1.mdifferentiableAt (hU.mem_nhds hz))
  change (mfderiv 𝓘(ℂ,E × F) 𝓘(ℂ,Model r × Model s) (e.chart ∘ f) z :
    (E × F) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart (f z)).comp
    (mfderiv 𝓘(ℂ,E × F) (model n) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  rw [h]
  exact ⟨fun v ↦ (e.horizontal _ (he hz) _).mp ((hf.2 z hz).1 v),
    fun w ↦ (e.vertical _ (he hz) _).mp ((hf.2 z hz).2 w)⟩

lemma SplittingChart.block_of_coordinate_tangencies (e : SplittingChart S)
    {U : Set (E × F)} (hU : IsOpen U) {f : E × F → Model r × Model s}
    (hf : DifferentiableOn ℂ f U) (hmap : MapsTo f U e.chart.target)
    (ht : ∀ z ∈ U, (∀ v : E, (fderiv ℂ f z (v,0)).2=0) ∧
      (∀ w : F, (fderiv ℂ f z (0,w)).1=0)) : IsBlockBox S U (e.chart.symm ∘ f) := by
  refine ⟨e.inverse_holomorphic.comp (mdifferentiableOn_iff_differentiableOn.mpr hf) hmap,?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hf.differentiableAt (hU.mem_nhds hz)))
  change (mfderiv 𝓘(ℂ,E × F) (model n) (e.chart.symm ∘ f) z : (E × F) →L[ℂ] Model n) =
    (mfderiv 𝓘(ℂ,Model r × Model s) (model n) e.chart.symm (f z)).comp
      (mfderiv 𝓘(ℂ,E × F) 𝓘(ℂ,Model r × Model s) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  constructor
  · intro v
    apply (e.horizontal _ (e.chart.map_target (hmap hz)) _).mpr
    rw [h]
    exact (e.inverse_derivative (hmap hz) (fderiv ℂ f z (v,0))) ▸ (ht z hz).1 v
  · intro w
    apply (e.vertical _ (e.chart.map_target (hmap hz)) _).mpr
    rw [h]
    exact (e.inverse_derivative (hmap hz) (fderiv ℂ f z (0,w))) ▸ (ht z hz).2 w

lemma SplittingChart.inverse_isBlockBox (e : SplittingChart S) :
    IsBlockBox S e.chart.target e.chart.symm := by
  simpa only [Function.comp_id] using e.block_of_coordinate_tangencies e.chart.open_target
    differentiable_id.differentiableOn (mapsTo_id _)
    (by intro z _; simp)

lemma SplittingChart.mix_block_maps (e : SplittingChart S) {U : Set (E × F)}
    (hU : IsOpen U) {f g : E × F → X.Carrier} (hf : IsBlockBox S U f) (hg : IsBlockBox S U g)
    (hfe : MapsTo f U e.chart.source) (hge : MapsTo g U e.chart.source) :
    IsBlockBox S U (fun z ↦ e.chart.symm ((e.chart (f z)).1,(e.chart (g z)).2)) := by
  have hfc := e.block_coordinates hU hf hfe
  have hgc := e.block_coordinates hU hg hge
  let k : E × F → Model r × Model s := fun z ↦ ((e.chart (f z)).1,(e.chart (g z)).2)
  have hk : DifferentiableOn ℂ k U := hfc.1.fst.prodMk hgc.1.snd
  apply e.block_of_coordinate_tangencies hU hk
  · intro z hz
    have hfT := e.chart.map_source (hfe hz)
    have hgT := e.chart.map_source (hge hz)
    rw [e.product_range] at hfT hgT ⊢
    exact ⟨hfT.1,hgT.2⟩
  · intro z hz
    have hd₁ := (hfc.1.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.fst
    have hd₂ := (hgc.1.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.snd
    have hd := (hd₁.prodMk hd₂).fderiv
    change fderiv ℂ k z = _ at hd
    rw [hd]
    exact ⟨fun v ↦ (hgc.2 z hz).1 v,fun w ↦ (hfc.2 z hz).2 w⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def IsHorizontalMap (S : HolomorphicSplitting X r s) (U : Set E) (f : E → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E) (model n) f U ∧ ∀ z ∈ U, ∀ v : E,
    S.projection (f z) (mfderiv 𝓘(ℂ,E) (model n) f z v) = mfderiv 𝓘(ℂ,E) (model n) f z v

def IsVerticalMap (S : HolomorphicSplitting X r s) (U : Set E) (f : E → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E) (model n) f U ∧ ∀ z ∈ U, ∀ v : E,
    S.projection (f z) (mfderiv 𝓘(ℂ,E) (model n) f z v) = 0

lemma IsHorizontalMap.comp {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsHorizontalMap S U f) {q : F → E}
    (hq : DifferentiableOn ℂ q V) (hmap : MapsTo q V U) : IsHorizontalMap S V (f ∘ q) := by
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hmap,?_⟩
  intro z hz v
  rw [mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq.differentiableAt (hV.mem_nhds hz)))]
  exact hf.2 _ (hmap hz) _

lemma IsVerticalMap.comp {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsVerticalMap S U f) {q : F → E}
    (hq : DifferentiableOn ℂ q V) (hmap : MapsTo q V U) : IsVerticalMap S V (f ∘ q) := by
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hmap,?_⟩
  intro z hz v
  rw [mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq.differentiableAt (hV.mem_nhds hz)))]
  exact hf.2 _ (hmap hz) _

lemma IsHorizontalMap.curve {U : Set ℂ} {f : ℂ → X.Carrier} (hf : IsHorizontalMap S U f) :
    IsHorizontalCurve S U f := ⟨hf.1,fun z hz ↦ hf.2 z hz 1⟩

lemma IsVerticalMap.curve {U : Set ℂ} {f : ℂ → X.Carrier} (hf : IsVerticalMap S U f) :
    IsVerticalCurve S U f := ⟨hf.1,fun z hz ↦ hf.2 z hz 1⟩

lemma IsHorizontalMap.block {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsHorizontalMap S U f) :
    IsBlockBox S (U ×ˢ V) (fun z : E × F ↦ f z.1) := by
  have hc := hf.comp hU (hU.prod hV) differentiable_fst.differentiableOn
    (show MapsTo Prod.fst (U ×ˢ V) U from fun _ h ↦ h.1)
  refine ⟨hc.1,fun z hz ↦ ⟨fun v ↦ hc.2 z hz (v,0),fun w ↦ ?_⟩⟩
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds hz.1))
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst)
  change (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.fst) z : (E × F) →L[ℂ] Model n) = _ at hd
  let P : Model n →L[ℂ] Model n := S.projection (f z.1)
  change P ((mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.fst) z : (E × F) →L[ℂ] Model n) (0,w)) = 0
  rw [hd]
  simp only [mfderiv_eq_fderiv,fderiv_fst]
  change P ((mfderiv 𝓘(ℂ,E) (model n) f z.1 : E →L[ℂ] Model n) 0) = 0
  rw [map_zero]
  exact P.map_zero

lemma IsVerticalMap.block {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : F → X.Carrier} (hf : IsVerticalMap S V f) :
    IsBlockBox S (U ×ˢ V) (fun z : E × F ↦ f z.2) := by
  have hc := hf.comp hV (hU.prod hV) differentiable_snd.differentiableOn
    (show MapsTo Prod.snd (U ×ˢ V) V from fun _ h ↦ h.2)
  refine ⟨hc.1,fun z hz ↦ ⟨fun v ↦ ?_,fun w ↦ hc.2 z hz (0,w)⟩⟩
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt (hV.mem_nhds hz.2))
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd)
  change (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) = _ at hd
  let P : Model n →L[ℂ] Model n := S.projection (f z.2)
  change P ((mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) (v,0)) =
    (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) (v,0)
  rw [hd]
  simp only [mfderiv_eq_fderiv,fderiv_snd]
  change P ((mfderiv 𝓘(ℂ,F) (model n) f z.2 : F →L[ℂ] Model n) 0) =
    (mfderiv 𝓘(ℂ,F) (model n) f z.2 : F →L[ℂ] Model n) 0
  rw [map_zero]
  exact P.map_zero

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F A B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup A] [NormedSpace ℂ A]
 [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma IsBlockBox.comp_parameters {U : Set E} {V : Set F} {W : Set A} {Z : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hZ : IsOpen Z)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f)
    {a : A → E} {b : B → F} (ha : DifferentiableOn ℂ a W) (hb : DifferentiableOn ℂ b Z)
    (hma : MapsTo a W U) (hmb : MapsTo b Z V) :
    IsBlockBox S (W ×ˢ Z) (f ∘ Prod.map a b) := by
  have hq : DifferentiableOn ℂ (Prod.map a b) (W ×ˢ Z) :=
    (ha.comp differentiable_fst.differentiableOn (fun _ h ↦ h.1)).prodMk
      (hb.comp differentiable_snd.differentiableOn (fun _ h ↦ h.2))
  have hqm : MapsTo (Prod.map a b) (W ×ˢ Z) (U ×ˢ V) := fun _ h ↦ ⟨hma h.1,hmb h.2⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hqm,?_⟩
  intro z hz
  have had := ha.differentiableAt (hW.mem_nhds hz.1)
  have hbd := hb.differentiableAt (hZ.mem_nhds hz.2)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hqm hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (HasFDerivAt.prodMap z had.hasFDerivAt hbd.hasFDerivAt).differentiableAt)
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (a z.1,b z.2)
  let P : Model n →L[ℂ] Model n := S.projection (f (a z.1,b z.2))
  let M : (A × B) →L[ℂ] Model n := mfderiv 𝓘(ℂ,A × B) (model n) (f ∘ Prod.map a b) z
  have hM : M = D.comp ((fderiv ℂ a z.1).prodMap (fderiv ℂ b z.2)) := by
    change M = D.comp (mfderiv 𝓘(ℂ,A × B) 𝓘(ℂ,E × F) (Prod.map a b) z) at hd
    rw [mfderiv_eq_fderiv,(HasFDerivAt.prodMap z had.hasFDerivAt hbd.hasFDerivAt).fderiv] at hd
    exact hd
  change (∀ v : A, P (M (v,0))=M (v,0)) ∧ (∀ w : B, P (M (0,w))=0)
  rw [hM]
  constructor
  · intro v
    change P (D (fderiv ℂ a z.1 v,fderiv ℂ b z.2 0))=D (fderiv ℂ a z.1 v,fderiv ℂ b z.2 0)
    rw [map_zero]
    exact (hf.2 (a z.1,b z.2) (hqm hz)).1 _
  · intro w
    change P (D (fderiv ℂ a z.1 0,fderiv ℂ b z.2 w))=0
    rw [map_zero]
    exact (hf.2 (a z.1,b z.2) (hqm hz)).2 _

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma IsBlockBox.horizontal_slice {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) {b : F} (hb : b ∈ V) :
    IsHorizontalMap S U (fun a ↦ f (a,b)) := by
  let q : E → E × F := fun a ↦ (a,b)
  have hq : Differentiable ℂ q := differentiable_id.prodMk (differentiable_const b)
  have hmap : MapsTo q U (U ×ˢ V) := fun _ h ↦ ⟨h,hb⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq.differentiableOn) hmap,?_⟩
  intro z hz v
  let P : Model n →L[ℂ] Model n := S.projection (f (z,b))
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (z,b)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq z))
  change (mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) =
    D.comp (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E × F) q z) at hd
  rw [mfderiv_eq_fderiv] at hd
  have hqd : fderiv ℂ q z=(ContinuousLinearMap.id ℂ E).prod 0 := by
    exact ((hasFDerivAt_id z).prodMk (hasFDerivAt_const b z)).fderiv
  rw [hqd] at hd
  change P ((mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) v)=
    (mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) v
  rw [hd]
  exact (hf.2 (z,b) ⟨hz,hb⟩).1 v

lemma IsBlockBox.vertical_slice {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) {a : E} (ha : a ∈ U) :
    IsVerticalMap S V (fun b ↦ f (a,b)) := by
  let q : F → E × F := fun b ↦ (a,b)
  have hq : Differentiable ℂ q := (differentiable_const a).prodMk differentiable_id
  have hmap : MapsTo q V (U ×ˢ V) := fun _ h ↦ ⟨ha,h⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq.differentiableOn) hmap,?_⟩
  intro z hz v
  let P : Model n →L[ℂ] Model n := S.projection (f (a,z))
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (a,z)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq z))
  change (mfderiv 𝓘(ℂ,F) (model n) (f ∘ q) z : F →L[ℂ] Model n) =
    D.comp (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,E × F) q z) at hd
  rw [mfderiv_eq_fderiv] at hd
  have hqd : fderiv ℂ q z=(0 : F →L[ℂ] E).prod (ContinuousLinearMap.id ℂ F) := by
    exact ((hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)).fderiv
  rw [hqd] at hd
  change P ((mfderiv 𝓘(ℂ,F) (model n) (f ∘ q) z : F →L[ℂ] Model n) v)=0
  rw [hd]
  exact (hf.2 (a,z) ⟨ha,hz⟩).2 v

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

abbrev Polydisk (d : ℕ) := ball (0 : Model d) (1 : ℝ)

def SplittingChart.unitMap (e : SplittingChart S) : Model r × Model s → X.Carrier :=
  fun z ↦ e.chart.symm ((e.radius : ℂ) • z.1,(e.radius : ℂ) • z.2)

lemma scale_mem_ball {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {z : Model d}
    (hz : z ∈ Polydisk d) : (ρ : ℂ) • z ∈ ball 0 ρ := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
  nlinarith

lemma unscale_mem_ball {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {z : Model d}
    (hz : z ∈ ball 0 ρ) : (ρ : ℂ)⁻¹ • z ∈ Polydisk d := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
  exact (inv_mul_lt_iff₀ hρ).mpr (by simpa using hz)

lemma SplittingChart.unitMap_block (e : SplittingChart S) :
    IsBlockBox S (Polydisk r ×ˢ Polydisk s) e.unitMap := by
  have he : IsBlockBox S (ball 0 e.radius ×ˢ ball 0 e.radius) e.chart.symm := by
    simpa only [e.product_range] using e.inverse_isBlockBox
  exact he.comp_parameters isOpen_ball isOpen_ball isOpen_ball isOpen_ball
    (differentiable_id.const_smul (e.radius : ℂ)).differentiableOn
    (differentiable_id.const_smul (e.radius : ℂ)).differentiableOn
    (fun _ h ↦ scale_mem_ball e.radius_pos h) (fun _ h ↦ scale_mem_ball e.radius_pos h)

lemma SplittingChart.unitMap_coordinates (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) :
    e.unitMap ((e.radius : ℂ)⁻¹ • (e.chart x).1,(e.radius : ℂ)⁻¹ • (e.chart x).2)=x := by
  have hr : (e.radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr e.radius_pos.ne'
  simpa only [SplittingChart.unitMap,smul_smul,mul_inv_cancel₀ hr,one_smul] using
    e.chart.left_inv hx

end UniversalCoverSplitting
end
end

end OAI
