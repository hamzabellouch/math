import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothOperations

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma continuous_binary_closure {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {T : X → Y → Z} (hT : Continuous (fun p : X × Y => T p.1 p.2))
    {S : Set X} {U : Set Y} {V : Set Z} (h : ∀ x∈S, ∀ y∈U, T x y∈V)
    {x : X} (hx : x∈closure S) {y : Y} (hy : y∈closure U) : T x y∈closure V := by
  have hb {x : X} (hx : x∈S) : T x y∈closure V := by
    have ht : (fun y => T x y) '' U ⊆ V := by
      rintro _ ⟨y,hy,rfl⟩; exact h x hx y hy
    exact (image_closure_subset_closure_image (hT.comp (continuous_const.prodMk continuous_id))).trans
      (closure_mono ht) ⟨y,hy,rfl⟩
  have ht : (fun x => T x y) '' S ⊆ closure V := by
    rintro _ ⟨x,hx,rfl⟩; exact hb hx
  have hh := (image_closure_subset_closure_image (hT.comp (continuous_id.prodMk continuous_const))).trans
    (closure_mono ht)
  simpa only [closure_closure,Function.comp_apply,id_eq] using hh ⟨x,hx,rfl⟩

lemma smoothJet_sub {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    smoothJet (f-g)=smoothJet f-smoothJet g := by
  ext x i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [smoothJet,gradient,fderiv_sub (hf x) (hg x)]

lemma chainDifference_smooth_compact (F : SmoothLipZero) {z w : JetSpace}
    (hz : z∈smoothJets) (hw : w∈compactSmoothJets) :
    F.onLp (z+w)-F.onLp z ∈ compactSmoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgc,hgs,hgm,rfl⟩ := hw
  let d : R3 → ℝ := F ∘ (f+g)-F ∘ f
  have hd : ContDiff ℝ (↑(⊤ : ℕ∞)) d := (F.smooth.comp (hf.add hg)).sub (F.smooth.comp hf)
  have hs : Function.support d ⊆ Function.support g := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support,not_not] at hx ⊢
    simp [d,hx]
  have hdc : HasCompactSupport d := hgc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hdm : tsupport d ⊆ ball := (closure_mono hs).trans hgs
  have he : F.onLp (hfm.toLp _+hgm.toLp _)-F.onLp (hfm.toLp _) =ᵐ[ballMeasure] smoothJet d := by
    filter_upwards [Lp.coeFn_sub (F.onLp (hfm.toLp _+hgm.toLp _)) (F.onLp (hfm.toLp _)),
      F.onLp_ae (hfm.toLp _+hgm.toLp _),F.onLp_ae (hfm.toLp _),
      Lp.coeFn_add (hfm.toLp _) (hgm.toLp _),hfm.coeFn_toLp,hgm.coeFn_toLp] with x hs h1 h2 ha hf' hg'
    rw [hs,Pi.sub_apply,h1,h2,ha,Pi.add_apply,hf',hg']
    have haJet := congrFun (smoothJet_add (hf.differentiable (by simp))
      (hg.differentiable (by simp))) x
    simp only [Pi.add_apply] at haJet
    rw [←haJet]
    rw [←smoothJet_comp (f := f+g) F.derivative ((hf.add hg).differentiable (by simp)) x,
      ←smoothJet_comp (f := f) F.derivative (hf.differentiable (by simp)) x]
    exact (congrFun (smoothJet_sub ((F.smooth.comp (hf.add hg)).differentiable (by simp))
      ((F.smooth.comp hf).differentiable (by simp))) x).symm
  have hm := MemLp.ae_eq he (Lp.memLp (F.onLp (hfm.toLp _+hgm.toLp _)-F.onLp (hfm.toLp _)))
  exact ⟨d,hd,hdc,hdm,hm,Lp.ext (he.trans hm.coeFn_toLp.symm)⟩

lemma chainDifference_H10 (F : SmoothLipZero) {z w : JetSpace}
    (hz : z∈H1Space) (hw : w∈zeroTraceAmbient) :
    F.onLp (z+w)-F.onLp z ∈ zeroTraceAmbient := by
  change z∈(H1Space : Set JetSpace) at hz
  change w∈(zeroTraceAmbient : Set JetSpace) at hw
  change _∈(zeroTraceAmbient : Set JetSpace)
  rw [H1Space_eq_closure] at hz
  rw [zeroTraceAmbient_eq_closure] at hw ⊢
  exact continuous_binary_closure
    ((F.onLp_continuous.comp (continuous_fst.add continuous_snd)).sub
      (F.onLp_continuous.comp continuous_fst))
    (fun _ hz _ hw => chainDifference_smooth_compact F hz hw) hz hw

lemma chain_trace_eq (F : SmoothLipZero) {u v : H1} (h : trace u=trace v) :
    trace (F.onH1 u)=trace (F.onH1 v) := by
  have hw : u-v∈H10 := (Submodule.Quotient.eq H10).mp h
  apply (Submodule.Quotient.eq H10).mpr
  change F.onLp u.val-F.onLp v.val∈zeroTraceAmbient
  have hh := chainDifference_H10 F v.property (show u.val-v.val∈zeroTraceAmbient from hw)
  simpa only [add_sub_cancel] using hh

abbrev weakValue (u : H1) (x : R3) : ℝ := jetValue (u.val x)

lemma jet_clipped_of_bound {M : ℝ} {z : JetFiber} (hz : |jetValue z|≤M) :
    jetSuperposition (clipOperation M) (deriv (clipOperation M)) z=z := by
  change jetLiftValue (clippedValue M (jetValue z)) +
    jetLiftGradient (deriv (clippedValue M) (jetValue z) • jetGradient z)=z
  rw [clippedValue_eq hz,clippedValue_deriv hz,one_smul,←jetFiber_decomposition]

lemma jetValue_product (z w : JetFiber) : jetValue (jetProduct z w)=jetValue z*jetValue w := by
  change jetValue z*jetValue w+0=_; simp

lemma jetGradient_product (z w : JetFiber) :
    jetGradient (jetProduct z w)=jetValue z • jetGradient w+jetValue w • jetGradient z := by
  ext i
  change 0+(jetValue z • jetGradient w+jetValue w • jetGradient z) i=
    (jetValue z • jetGradient w+jetValue w • jetGradient z) i
  simp

theorem exists_H1_product {u v : H1} {M N : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hv : ∀ᵐ x ∂ballMeasure, |weakValue v x|≤N) :
    ∃ p : H1,
      (∀ᵐ x ∂ballMeasure, weakValue p x=weakValue u x*weakValue v x) ∧
      (∀ᵐ x ∂ballMeasure, weakGradient p x=
        weakValue u x • weakGradient v x+weakValue v x • weakGradient u x) ∧
      (v∈H10 → p∈H10) := by
  obtain ⟨A,hA,hca⟩ := exists_clippedValue_bound M
  obtain ⟨B,hB,hcb⟩ := exists_clippedValue_bound N
  let F := clipOperation M
  let G := clipOperation N
  let p : H1 := ⟨clippedProductLp F G A B u.val v.val,
    clippedProductLp_preserves_H1 F G A B u.property v.property⟩
  have he : p.val =ᵐ[ballMeasure] fun x => jetProduct (u.val x) (v.val x) := by
    filter_upwards [clippedProductLp_ae F G A B hA.le hB.le hca hcb u.val v.val,hu,hv]
      with x hx hy hz
    exact hx.trans (by rw [jet_clipped_of_bound hy,jet_clipped_of_bound hz])
  refine ⟨p,?_,?_,?_⟩
  · filter_upwards [he] with x hx
    exact congrArg jetValue hx |>.trans (jetValue_product _ _)
  · filter_upwards [he] with x hx
    exact congrArg jetGradient hx |>.trans (jetGradient_product _ _)
  · intro hv0
    exact clippedProductLp_preserves_H10 F G A B hA.le hB.le hca hcb u.property hv0

lemma smoothJet_constant (r : ℝ) : smoothJet (fun _ : R3 => r)=fun _ => jetLiftValue r := by
  ext x i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [smoothJet,gradient,jetLiftValue]

lemma constantJet_memLp (r : ℝ) : MemLp (smoothJet (fun _ : R3 => r)) 2 ballMeasure := by
  rw [smoothJet_constant]
  exact memLp_const _

def constantH1 (r : ℝ) : H1 :=
  ⟨(constantJet_memLp r).toLp _,(Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨fun _ => r,contDiff_const,constantJet_memLp r,rfl⟩)⟩

lemma constantH1_value (r : ℝ) : weakValue (constantH1 r) =ᵐ[ballMeasure] fun _ => r := by
  filter_upwards [(constantJet_memLp r).coeFn_toLp] with x hx
  change jetValue ((constantJet_memLp r).toLp _ x)=r
  rw [hx]; rfl

lemma constantH1_gradient (r : ℝ) : weakGradient (constantH1 r) =ᵐ[ballMeasure] 0 := by
  filter_upwards [(constantJet_memLp r).coeFn_toLp] with x hx
  change jetGradient ((constantJet_memLp r).toLp _ x)=0
  rw [hx,smoothJet_constant]
  ext i; rfl

lemma weakValue_add (u v : H1) : weakValue (u+v) =ᵐ[ballMeasure] weakValue u+weakValue v := by
  filter_upwards [Lp.coeFn_add u.val v.val] with x hx
  change jetValue ((u.val+v.val) x)=jetValue (u.val x)+jetValue (v.val x)
  rw [hx,Pi.add_apply,map_add]

lemma weakValue_sub (u v : H1) : weakValue (u-v) =ᵐ[ballMeasure] weakValue u-weakValue v := by
  filter_upwards [Lp.coeFn_sub u.val v.val] with x hx
  change jetValue ((u.val-v.val) x)=jetValue (u.val x)-jetValue (v.val x)
  rw [hx,Pi.sub_apply,map_sub]

lemma weakValue_smul (r : ℝ) (u : H1) : weakValue (r • u) =ᵐ[ballMeasure] r • weakValue u := by
  filter_upwards [Lp.coeFn_smul r u.val] with x hx
  change jetValue ((r • u.val) x)=r*jetValue (u.val x)
  rw [hx,Pi.smul_apply,map_smul]; rfl

lemma weakGradient_add (u v : H1) : weakGradient (u+v) =ᵐ[ballMeasure] weakGradient u+weakGradient v := by
  filter_upwards [Lp.coeFn_add u.val v.val] with x hx
  change jetGradient ((u.val+v.val) x)=jetGradient (u.val x)+jetGradient (v.val x)
  rw [hx,Pi.add_apply,map_add]

lemma weakGradient_sub (u v : H1) : weakGradient (u-v) =ᵐ[ballMeasure] weakGradient u-weakGradient v := by
  filter_upwards [Lp.coeFn_sub u.val v.val] with x hx
  change jetGradient ((u.val-v.val) x)=jetGradient (u.val x)-jetGradient (v.val x)
  rw [hx,Pi.sub_apply,map_sub]

lemma weakGradient_smul (r : ℝ) (u : H1) : weakGradient (r • u) =ᵐ[ballMeasure] r • weakGradient u := by
  filter_upwards [Lp.coeFn_smul r u.val] with x hx
  change jetGradient ((r • u.val) x)=r • jetGradient (u.val x)
  rw [hx,Pi.smul_apply,map_smul]

end ScalarConductivity

end

end OAI
