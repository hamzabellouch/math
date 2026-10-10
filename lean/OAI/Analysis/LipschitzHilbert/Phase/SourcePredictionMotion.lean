import OAI.Analysis.LipschitzHilbert.Phase.AngularMassMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskMotion

namespace OAI

/-! Mass rescaling and block-transition motion for the snapshot prediction.
Every estimate is relative to the positive snapshot masses; no positive
lower cutoff is imposed on a mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def massPowerScale (n c a b : ℝ) : ℝ := n^a*c^b

theorem massPowerScale_pos {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    0 < massPowerScale n c a b := mul_pos (Real.rpow_pos_of_pos hn a) (Real.rpow_pos_of_pos hc b)

theorem massPowerScale_exp {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    massPowerScale n c a b = Real.exp (a*Real.log n+b*Real.log c) := by
  rw [massPowerScale, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hc, ← Real.exp_add]
  congr 1
  ring

theorem massPowerScale_relative_motion {n n' c c' δ : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c') (hδ : 0 ≤ δ)
    (hN : |Real.log n'-Real.log n| ≤ δ) (hC : |Real.log c'-Real.log c| ≤ δ)
    (a b : ℝ) :
    let E := (|a|+|b|)*δ
    |massPowerScale n' c' a b/massPowerScale n c a b-1| ≤ Real.exp E*E := by
  dsimp only
  have harg : |(a*Real.log n'+b*Real.log c')-(a*Real.log n+b*Real.log c)| ≤
      (|a|+|b|)*δ := by
    calc
      _ = |a*(Real.log n'-Real.log n)+b*(Real.log c'-Real.log c)| := by congr 1; ring
      _ ≤ |a*(Real.log n'-Real.log n)|+|b*(Real.log c'-Real.log c)| := abs_add_le _ _
      _ = |a| * |Real.log n'-Real.log n|+|b| * |Real.log c'-Real.log c| := by
        rw [abs_mul,abs_mul]
      _ ≤ |a| * δ+|b| * δ := add_le_add (mul_le_mul_of_nonneg_left hN (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
      _ = _ := by ring
  have h := exponential_relative_motion
    (a := ((a*Real.log n+b*Real.log c : ℝ):ℂ))
    (b := ((a*Real.log n'+b*Real.log c' : ℝ):ℂ))
    (show 0 ≤ (|a|+|b|)*δ by positivity)
    (by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using harg)
  rw [massPowerScale_exp hn' hc',massPowerScale_exp hn hc]
  simpa only [← Complex.ofReal_exp,← Complex.ofReal_div,← Complex.ofReal_one,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem positive_relative_motion_to_sub {s s' q : ℝ} (hs : 0 < s)
    (h : |s'/s-1| ≤ q) : |s'-s| ≤ q*s := by
  have heq : s'/s-1 = (s'-s)/s := by field_simp [hs.ne']
  rw [heq,abs_div,abs_of_pos hs] at h
  exact (div_le_iff₀ hs).mp h

theorem complex_relative_motion_to_sub {lam lam' : ℂ} {q : ℝ} (hlam : lam ≠ 0)
    (h : ‖lam'/lam-1‖ ≤ q) : ‖lam'-lam‖ ≤ q*‖lam‖ := by
  have heq : lam'/lam-1 = (lam'-lam)/lam := by field_simp [hlam]
  rw [heq,norm_div] at h
  exact (div_le_iff₀ (norm_pos_iff.mpr hlam)).mp h

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar and vector errors are kept separate until the final product.
The reference vector may already have been rotated by a diagonal isometry. -/
theorem scalar_rescaling_motion {s s' c q η C : ℝ}
    (hs : 0 < s) (hs' : 0 ≤ s') (_hc : 0 ≤ c) (hq : 0 ≤ q)
    (_hη : 0 ≤ η) (_hC : 0 ≤ C) (hscale : |s'/s-1| ≤ q)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    ‖s' • v'-s • v‖ ≤ ((1+q)*η+q*C)*s*c := by
  have hsub := positive_relative_motion_to_sub hs hscale
  have hsbound : s' ≤ (1+q)*s := by linarith [(abs_le.mp hsub).2]
  have heq : s' • v'-s • v = s' • (v'-v)+(s'-s) • v := by
    rw [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖s' • (v'-v)‖+‖(s'-s) • v‖ := norm_add_le _ _
    _ = s'*‖v'-v‖+|s'-s| * ‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hs']
    _ ≤ ((1+q)*s)*(η*c)+(q*s)*(C*c) := add_le_add
      (mul_le_mul hsbound hmotion (norm_nonneg _) (by positivity))
      (mul_le_mul hsub hv (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem massPowerScale_amplitude_motion {n n' c c' δ η C : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hN : |Real.log n'-Real.log n| ≤ δ) (hchild : |Real.log c'-Real.log c| ≤ δ)
    (a b : ℝ) (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    let q := Real.exp ((|a|+|b|)*δ)*((|a|+|b|)*δ)
    ‖massPowerScale n' c' a b • v'-massPowerScale n c a b • v‖ ≤
      ((1+q)*η+q*C)*massPowerScale n c a b*c := by
  dsimp only
  exact scalar_rescaling_motion (massPowerScale_pos hn hc a b)
    (massPowerScale_pos hn' hc' a b).le hc.le (by positivity) hη hC
    (massPowerScale_relative_motion hn hn' hc hc' hδ hN hchild a b) v' v hv hmotion

end Vector

/-- The scalar in `pred:scaled-motion` times the snapshot child mass. -/
theorem prediction_mass_scale_identity {n c : ℝ} (hn : 0 < n) (hc : 0 < c)
    (p μ : ℝ) :
    massPowerScale n c (-(1/p)) (μ-1+1/p)*c = (c/n)^(1/p)*c^μ := by
  rw [massPowerScale,Real.rpow_neg hn.le,Real.div_rpow hc.le hn.le]
  have heq : c^(μ-1+1/p)*c = c^(1/p)*c^μ := by
    calc
      _ = c^(μ-1+1/p)*c^(1:ℝ) := by rw [Real.rpow_one]
      _ = c^((μ-1+1/p)+1) := (Real.rpow_add hc _ _).symm
      _ = c^(1/p+μ) := by congr 1; ring
      _ = _ := Real.rpow_add hc _ _
  calc
    (n^(1/p))⁻¹*c^(μ-1+1/p)*c = (n^(1/p))⁻¹*(c^(μ-1+1/p)*c) := by ring
    _ = (n^(1/p))⁻¹*(c^(1/p)*c^μ) := by rw [heq]
    _ = _ := by ring

theorem prediction_numerator_scale_identity {n c : ℝ} (hn : 0 < n) (μ : ℝ) :
    n^(μ-1)*c = n^μ*(c/n) := by
  rw [Real.rpow_sub hn,Real.rpow_one]
  ring

theorem complex_product_relative_motion {s s' q η : ℝ} (hs : 0 < s) (hs' : 0 ≤ s')
    (hq : 0 ≤ q) (_hη : 0 ≤ η) (hscale : |s'/s-1| ≤ q)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ 1) (hlammove : ‖lam'-lam‖ ≤ η) :
    ‖(s':ℂ)*lam'-(s:ℂ)*lam‖ ≤ (q+η+q*η)*s := by
  have hsub := positive_relative_motion_to_sub hs hscale
  have hsbound : s' ≤ (1+q)*s := by linarith [(abs_le.mp hsub).2]
  have heq : (s':ℂ)*lam'-(s:ℂ)*lam = ((s':ℂ)-(s:ℂ))*lam+(s':ℂ)*(lam'-lam) := by ring
  rw [heq]
  calc
    _ ≤ ‖((s':ℂ)-(s:ℂ))*lam‖+‖(s':ℂ)*(lam'-lam)‖ := norm_add_le _ _
    _ = |s'-s| * ‖lam‖+s'*‖lam'-lam‖ := by
      rw [norm_mul,norm_mul,← Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hs']
    _ ≤ (q*s)*1+((1+q)*s)*η := add_le_add
      (mul_le_mul hsub hlam (norm_nonneg _) (by positivity))
      (mul_le_mul hsbound hlammove (norm_nonneg _) (by positivity))
    _ = _ := by ring

section ComplexVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complex_coefficient_amplitude_motion {s c q η C : ℝ}
    (hs : 0 ≤ s) (_hc : 0 ≤ c) (hq : 0 ≤ q) (_hη : 0 ≤ η) (_hC : 0 ≤ C)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ s) (hlammove : ‖lam'-lam‖ ≤ q*s)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    ‖lam' • v'-lam • v‖ ≤ ((1+q)*η+q*C)*s*c := by
  have hlam' : ‖lam'‖ ≤ (1+q)*s := by
    have ht := norm_add_le (lam'-lam) lam
    rw [sub_add_cancel] at ht
    nlinarith
  have heq : lam' • v'-lam • v = lam' • (v'-v)+(lam'-lam) • v := by
    rw [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖lam' • (v'-v)‖+‖(lam'-lam) • v‖ := norm_add_le _ _
    _ = ‖lam'‖*‖v'-v‖+‖lam'-lam‖*‖v‖ := by rw [norm_smul,norm_smul]
    _ ≤ ((1+q)*s)*(η*c)+(q*s)*(C*c) := add_le_add
      (mul_le_mul hlam' hmotion (norm_nonneg _) (by positivity))
      (mul_le_mul hlammove hv (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The numerator rescaling in `pred:numerator-motion`. Its coefficient
is expressed relative to `n^μ*(c/n)`, exactly the snapshot parent scale
times the child fraction. -/
theorem prediction_numerator_motion {n n' c δ qlam η C : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hqlam : 0 ≤ qlam) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hN : |Real.log n'-Real.log n| ≤ δ) (μ : ℝ)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ 1) (hlammove : ‖lam'-lam‖ ≤ qlam)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    let qn := Real.exp (|μ-1| * δ)*(|μ-1| * δ)
    let q := qn+qlam+qn*qlam
    ‖((n'^(μ-1):ℝ):ℂ) • (lam' • v')-((n^(μ-1):ℝ):ℂ) • (lam • v)‖ ≤
      ((1+q)*η+q*C)*n^μ*(c/n) := by
  dsimp only
  let qn := Real.exp (|μ-1| * δ)*(|μ-1| * δ)
  have hqn : 0 ≤ qn := by dsimp [qn]; positivity
  have hscale : |n'^(μ-1)/n^(μ-1)-1| ≤ qn := by
    simpa only [massPowerScale,Real.rpow_zero,mul_one,abs_zero,add_zero] using
      massPowerScale_relative_motion hn hn' (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1) hδ hN (by simp; exact hδ) (μ-1) 0
  have hproduct := complex_product_relative_motion (Real.rpow_pos_of_pos hn (μ-1))
    (Real.rpow_pos_of_pos hn' (μ-1)).le hqn hqlam hscale lam lam' hlam hlammove
  have hnorm : ‖((n^(μ-1):ℝ):ℂ)*lam‖ ≤ n^(μ-1) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn (μ-1))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlam
      (Real.rpow_pos_of_pos hn (μ-1)).le
  have h := complex_coefficient_amplitude_motion (Real.rpow_pos_of_pos hn (μ-1)).le hc
    (show 0 ≤ qn+qlam+qn*qlam by positivity) hη hC _ _ hnorm hproduct v' v hv hmotion
  rw [smul_smul,smul_smul]
  calc
    _ ≤ ((1+(qn+qlam+qn*qlam))*η+(qn+qlam+qn*qlam)*C)*n^(μ-1)*c := h
    _ = _ := by rw [mul_assoc, prediction_numerator_scale_identity hn]; ring

end ComplexVector

namespace AngularGrid

theorem source_path_product_ne_zero {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X)
    (lower upper : ℕ) (s : ℝ) :
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper s ≠ 0 := by
  unfold packetPathProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Complex.exp_ne_zero _

theorem source_path_product_norm_le_one {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X)
    (lower upper : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) upper)
    (hphase : ∀ j ∈ Finset.Ico lower upper, 0 ≤ (phase j).re) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper (slope top)‖ ≤ 1 := by
  rw [packetPathProduct,norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.Ico lower upper, (1:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact norm_nonneg _
      · intro j hj
        exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase x j top
          htop (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he) (hphase j hj)
    _ = _ := by simp

/-- Actual parent and child submasses supply the scalar part of
`pred:scaled-motion`; the vector error is the already proved physical
amplitude motion. The chosen boundary ancestor may precede the block. -/
theorem source_scaled_prediction_motion {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (parentSet childSet : Finset ι) (hsub : childSet ⊆ parentSet)
    (hne : childSet.Nonempty)
    (hparent : parentSet ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (p μ η C : ℝ) (hη : 0 ≤ η) (hC : 0 ≤ C) (v' v : E) :
    let mass := fun S x => ∑ t ∈ S, (T t).weight K D x
    let n := mass parentSet z
    let c := mass childSet z
    let n' := mass parentSet (SlopeBox.lineShift sR b z)
    let c' := mass childSet (SlopeBox.lineShift sR b z)
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    let e := (|-(1/p)|+|μ-1+1/p|)*δ
    let q := Real.exp e*e
    ‖v‖ ≤ C*c → ‖v'-v‖ ≤ η*c →
    ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • v'-
      massPowerScale n c (-(1/p)) (μ-1+1/p) • v‖ ≤
      ((1+q)*η+q*C)*(c/n)^(1/p)*c^μ := by
  classical
  dsimp only
  let mass := fun (S : Finset ι) x => ∑ t ∈ S, (T t).weight K D x
  have hpos (S : Finset ι) (hS : S.Nonempty) (x : ℝ × ℝ) : 0 < mass S x := by
    apply Finset.sum_pos'
    · intro t _
      exact (T t).weight_pos hK D x |>.le
    · obtain ⟨t,ht⟩ := hS
      exact ⟨t,ht,(T t).weight_pos hK D x⟩
  have hparentne : parentSet.Nonempty := hne.mono hsub
  have hmN := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
    base h i hhi gap hgap0 hgap s sR hs child hchild hblock parentSet hparentne hparent b hb z
  have hmC := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
    base h i hhi gap hgap0 hgap s sR hs child hchild hblock childSet hne (hsub.trans hparent) b hb z
  intro hv hmove
  have hresult := massPowerScale_amplitude_motion
    (hpos parentSet hparentne z) (hpos parentSet hparentne (SlopeBox.lineShift sR b z))
    (hpos childSet hne z) (hpos childSet hne (SlopeBox.lineShift sR b z))
    (show 0 ≤ (5*D/K)/Real.sqrt (g.branching:ℝ) by positivity)
    hη hC hmN hmC (-(1/p)) (μ-1+1/p) v' v hv hmove
  calc
    _ ≤ ((1+Real.exp ((|-(1/p)|+|μ-1+1/p|)*((5*D/K)/Real.sqrt (g.branching:ℝ)))*
        ((|-(1/p)|+|μ-1+1/p|)*((5*D/K)/Real.sqrt (g.branching:ℝ))))*η+
      (Real.exp ((|-(1/p)|+|μ-1+1/p|)*((5*D/K)/Real.sqrt (g.branching:ℝ)))*
        ((|-(1/p)|+|μ-1+1/p|)*((5*D/K)/Real.sqrt (g.branching:ℝ))))*C)*
      massPowerScale (mass parentSet z) (mass childSet z) (-(1/p)) (μ-1+1/p)*
      mass childSet z := hresult
    _ = _ := by
      rw [mul_assoc, prediction_mass_scale_identity (hpos parentSet hparentne z) (hpos childSet hne z)]
      ring

/-- The actual finite source transition product has relative motion
obtained from physical child and boundary masses, without any mass cutoff. -/
theorem source_block_transition_relative_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (h lower upper : ℕ) (hbase : h ≤ lower)
    (hgap : ∀ j ∈ Finset.Ico lower upper, 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) upper)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (Z : ℝ) (hZ : 0 ≤ Z) (hphase : ∀ j ∈ Finset.Ico lower upper, ‖phase j‖ ≤ Z) :
    let weight := fun t x => (T t).weight K D x
    let lam := fun x => g.packetPathProduct (g.sourceTransition tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap phase x)
      lower upper (T top).slope
    let e := (upper-lower:ℕ)*Z*(2*((5*D/K)/Real.sqrt (g.branching:ℝ)))
    ‖lam (SlopeBox.lineShift sR b z)/lam z-1‖ ≤ Real.exp e*e := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight K D x
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  apply g.source_path_relative_motion tops slope precision cutoff weight hp
    (fun t x => (T t).weight_pos hK D x) hKb gap phase lower upper top htop he
    z (SlopeBox.lineShift sR b z) Z ((5*D/K)/Real.sqrt (g.branching:ℝ)) hZ
    (by positivity) hphase
  · intro j hj
    let A := g.cellTops tops slope precision cutoff (j+1) (g.index (j+1) (T top).slope)
    have hA : A.Nonempty := ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he⟩⟩
    exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      0 h (j+1) (by have := (Finset.mem_Ico.mp hj).1; omega)
      (gap j) (hgap j hj).1 (hgap j hj).2 (T top).slope sR hs child hchild hblock
      A hA (g.parent_subset_boundary tops slope precision cutoff 0 (j+1) (gap j) (T top).slope) b hb z
  · intro j hj
    let A := g.boundaryTops tops slope precision cutoff (j+1-Kb) j (gap j) (T top).slope
    have hA : A.Nonempty := by
      apply Finset.Nonempty.mono (g.parent_subset_boundary tops slope precision cutoff
        (j+1-Kb) j (gap j) (T top).slope)
      exact ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
        ⟨htop,rfl,g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he⟩⟩
    have hmass := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      (j+1-Kb) h j (by have := (Finset.mem_Ico.mp hj).1; omega)
      (gap j) (hgap j hj).1 (hgap j hj).2 (T top).slope sR hs child hchild hblock
      A hA (Finset.Subset.refl _) b hb z
    rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap,
      g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap]
    exact hmass

end AngularGrid

end LipschitzHilbert

end

end OAI
