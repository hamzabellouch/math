import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorEnvelope
import OAI.Analysis.LipschitzHilbert.Phase.AngularErrorConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.ActualErrorConvolution

namespace OAI

/-! Angular errors are summed over their active labels at the source
point, before the lattice convolution. Consequently the wide reference
cone contributes no factor counting all available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- Pointwise domination of the sum of sources passes through the
common positive convolution, with the same constant. -/
theorem sum_planarPositiveConvolution_le_source {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b)) (hf0 : ∀ b z, 0 ≤ f b z)
    (source : ℝ×ℝ → ℝ) (hs : Measurable source) (hs0 : ∀ z, 0 ≤ source z)
    {l W C B : ℝ} (hl : 0 < l) (hW : 0 < W) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hsB : ∀ z, source z ≤ B) (hoverlap : ∀ z, ∑ b, f b z ≤ C*source z)
    (x y : ℝ) :
    (∑ b, planarPositiveConvolution l W (f b) x y) ≤
      C*planarPositiveConvolution l W source x y := by
  have hsum0 (z : ℝ×ℝ) : 0 ≤ ∑ b, f b z := Finset.sum_nonneg (fun b _ => hf0 b z)
  have hsumB (z : ℝ×ℝ) : (∑ b, f b z) ≤ C*B :=
    (hoverlap z).trans (mul_le_mul_of_nonneg_left (hsB z) hC)
  have hfb (b : Λ) (z : ℝ×ℝ) : ‖f b z‖ ≤ C*B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 b z)]
    exact (Finset.single_le_sum (fun a _ => hf0 a z) (Finset.mem_univ b)).trans (hsumB z)
  rw [← planarPositiveConvolution_sum f hf hl hW hfb]
  calc
    _ ≤ planarPositiveConvolution l W (fun z => C*source z) x y := by
      apply integral_mono
        (planarPositiveConvolution_integrable l W _
          (Finset.measurable_sum _ (fun b _ => hf b)) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hsum0 z)]; exact hsumB z) x y)
        (planarPositiveConvolution_integrable l W _ (hs.const_mul C) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (hs0 z))]
                       exact mul_le_mul_of_nonneg_left (hsB z) hC) x y)
      intro z
      exact mul_le_mul_of_nonneg_left (hoverlap z)
        (mul_nonneg (lineKernel_nonneg _ _ hl) (lineKernel_nonneg _ _ hW))
    _ = _ := planarPositiveConvolution_const_mul l W C source x y

/-- The actual coefficient error for a finite family of translated
lattices. Only active selector labels enter the source overlap. -/
theorem source_labeled_error_convolution {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY slope : Λ → ℝ) {l W d radius C M Lip small wide : ℝ} {K H : ℕ}
    (hl : 0 < l) (hW : 0 < W) (hd : 0 < d)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hLip : 0 ≤ Lip)
    (hsmall : 0 < small) (hsmall1 : small ≤ 1) (hwide : 1 ≤ wide)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ slope d H) (hK : radius ≤ K)
    (selector : Λ → κ → ℝ → ℂ) (hselector : ∀ b k, Measurable (selector b k))
    (hselectorBound : ∀ b k s, ‖selector b k s‖ ≤ M)
    (hsupport : ∀ b k s, selector b k s ≠ 0 → |s-slope b| ≤ radius*d)
    (direction : ℝ×ℝ → ℝ) (hdirection : Measurable direction) (t : ℝ)
    (hnear : ∀ b k s, |s-t| ≤ small*d →
      ‖selector b k s-selector b k t‖ ≤ Lip*(|s-t|/d))
    (hfar : ∀ b k s, wide*d < |s-t| → selector b k s = 0)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hwaveBound : ∀ b i k z, ‖wave b i k z‖ ≤
      C*tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W)
      (angularErrorWave (fun _ k => selector b k) (wave b) direction t d) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
      (64*(4*Real.pi)^2)*
        (2*((2*K+1)*H):ℕ)*
        planarPositiveConvolution l W
          (fun p => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|) z.1 z.2 := by
  classical
  let active := fun (b : Λ) (p : ℝ×ℝ) =>
    (∃ k, selector b k (direction p) ≠ 0) ∨ (∃ k, selector b k t ≠ 0)
  let common := fun p : ℝ×ℝ => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|
  let source := fun b p => if active b p then common p else 0
  have hA : 0 ≤ C*(2*M+Lip) := mul_nonneg hC (by linarith)
  have hcommon0 (p : ℝ×ℝ) : 0 ≤ common p :=
    mul_nonneg hA (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _))
  have hcommon : Measurable common := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hcommonB (p : ℝ×ℝ) : common p ≤ (C*(2*M+Lip))*(1+small) :=
    mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hsmall hd (abs_nonneg _)) hA
  have hsource0 (b : Λ) (p : ℝ×ℝ) : 0 ≤ source b p := by
    dsimp [source]
    split_ifs
    · exact hcommon0 p
    · exact le_rfl
  have hsourceMeas (b : Λ) : Measurable (source b) := by
    have ha : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} := by
      have heq : {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} =
          ⋃ k : κ, {p | selector b k (direction p) ≠ 0} := by ext p; simp
      rw [heq]
      exact MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun ((hselector b k).comp hdirection) measurable_const).compl
    have hb : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k t ≠ 0} := by
      by_cases hb : ∃ k, selector b k t ≠ 0 <;> simp [hb]
    exact Measurable.ite (ha.union hb) hcommon measurable_const
  have hoverlap (p : ℝ×ℝ) : (∑ b, source b p) ≤ (2*((2*K+1)*H):ℕ)*common p := by
    let U := SourceSlopeLabels.active Finset.univ selector (direction p) ∪
      SourceSlopeLabels.active Finset.univ selector t
    have hmem (b : Λ) : active b p ↔ b ∈ U := by
      simp only [active,U,SourceSlopeLabels.active,Finset.mem_union,Finset.mem_filter,
        Finset.mem_univ,true_and]
    have hsum : (∑ b, source b p) = (U.card:ℝ)*common p := by
      simp only [source,hmem]
      rw [← Finset.sum_filter]
      have heq : Finset.univ.filter (fun b => b ∈ U) = U := by ext b; simp
      rw [heq]
      simp only [Finset.sum_const,nsmul_eq_mul]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right _ (hcommon0 p)
    exact_mod_cast SourceSlopeLabels.active_union_card_le Finset.univ slope selector
      hd hlocal hK (fun b _ k s => hsupport b k s)
  have hbound (b : Λ) (i : ι b) (k : κ) (p : ℝ×ℝ) :
      ‖angularErrorWave (fun _ k => selector b k) (wave b) direction t d i k p‖ ≤
        tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 p*source b p := by
    by_cases ha : active b p
    · have he := multiplierError_bound (selector b k) t d small wide M Lip (direction p)
        hd hsmall hsmall1 hwide hM hLip (hselectorBound b k)
        (hnear b k (direction p)) (hfar b k (direction p))
      rw [angularErrorWave,norm_mul]
      have hm := mul_le_mul he (hwaveBound b i k p) (norm_nonneg _)
        (mul_nonneg (by linarith) (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _)))
      convert hm using 1
      dsimp [source,common]
      rw [ite_eq_left ha]
      ring
    · have hu : selector b k (direction p) = 0 := by
        by_contra hu
        exact ha (Or.inl ⟨k,hu⟩)
      have ht : selector b k t = 0 := by
        by_contra ht
        exact ha (Or.inr ⟨k,ht⟩)
      simp only [angularErrorWave,multiplierError,hu,ht,ite_self,sub_self,zero_mul,norm_zero]
      exact mul_nonneg (tileEnvelope_nonneg _ _ _ _ _ _) (hsource0 b p)
  have hB : 0 ≤ (C*(2*M+Lip))*(1+small) := mul_nonneg hA (by linarith)
  have hfb (b : Λ) (p : ℝ×ℝ) : ‖source b p‖ ≤ (C*(2*M+Lip))*(1+small) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hsource0 b p)]
    dsimp [source]
    split_ifs
    · exact hcommonB p
    · exact hB
  calc
    _ ≤ ∑ b, (64*(4*Real.pi)^2)*planarPositiveConvolution l W (source b) z.1 z.2 := by
      apply Finset.sum_le_sum
      intro b _
      exact lattice_coefficient_convolution (site b) (hinj b) (originX b) (originY b) l W
        hl hW (source b) (hsourceMeas b) (hsource0 b) (hfb b)
        _ (angularErrorWave_measurable _ _ _ _ _ (fun i k => hselector b k) (hwave b) hdirection)
        (hbound b) g hg hg1 z
    _ = (64*(4*Real.pi)^2)*∑ b, planarPositiveConvolution l W (source b) z.1 z.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (64*(4*Real.pi)^2)*((2*((2*K+1)*H):ℕ)*planarPositiveConvolution l W common z.1 z.2) :=
      mul_le_mul_of_nonneg_left
        (sum_planarPositiveConvolution_le_source source hsourceMeas hsource0 common hcommon hcommon0
          hl hW (by positivity) hB hcommonB hoverlap z.1 z.2) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
