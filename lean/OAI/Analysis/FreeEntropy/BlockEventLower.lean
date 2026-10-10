import OAI.Analysis.FreeEntropy.MatrixHeatLaw

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem normalLaw_rotated_mask_markov {s r : ℝ} (hs : 0<s) (hr : 0<r)
    (f : Fin d → Fin p) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} ≤
      ENNReal.ofReal (s*(blockMask f).card/r^2) := by
  have hm := normalLaw_measurePreserving s (rotateLinearIsometryEquiv (n := p+1) U)
  have hE : MeasurableSet {a : MatrixCoordinates (p+1) d | r≤‖coordinateMask (blockMask f) a‖} :=
    (isClosed_le continuous_const (coordinateMask_continuous _).norm).measurableSet
  have he := hm.measure_preimage hE.nullMeasurableSet
  change (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} = _ at he
  rw [he]
  exact normalLaw_coordinateMask_markov hs hr _
 theorem coordinateMask_univ {ι : Type u1} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    coordinateMask univ x=x := by ext i; simp [coordinateMask]
 theorem normalLaw_norm_markov {ι : Type u2} [Fintype ι] [DecidableEq ι] {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (normalLaw (ι := ι) s) {a | r≤‖a‖} ≤ ENNReal.ofReal (s*Fintype.card ι/r^2) := by
  simpa only [coordinateMask_univ,card_univ] using normalLaw_coordinateMask_markov (ι := ι) hs hr univ
 theorem blockEvent_add_mem {r A B M : ℝ} (hAB : A+B≤M)
    (a g : MatrixCoordinates (p+1) d) (ha : ‖a‖≤A) (hg : ‖g‖≤B)
    (f : Fin d → Fin p) (hf : balancedBlocks f) (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (ha' : 2*r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖)
    (hg' : ‖coordinateMask (blockMask f) (rotateCoordinates U g)‖≤r) :
    a+g∈blockEvent p d r M := by
  refine ⟨(norm_add_le _ _).trans ((add_le_add ha hg).trans hAB),f,hf,U,?_⟩
  have he : coordinateMask (blockMask f) (rotateCoordinates U (a+g))=
      coordinateMask (blockMask f) (rotateCoordinates U a)+coordinateMask (blockMask f) (rotateCoordinates U g) := by
    have hr := (rotateLinearIsometryEquiv (n := p+1) U).map_add a g
    change rotateCoordinates U (a+g)=rotateCoordinates U a+rotateCoordinates U g at hr
    rw [hr]
    exact (coordinateMaskLinear (blockMask f)).map_add _ _
  have hr := norm_sub_norm_le (coordinateMask (blockMask f) (rotateCoordinates U a))
    (-coordinateMask (blockMask f) (rotateCoordinates U g))
  simp only [norm_neg,sub_neg_eq_add] at hr
  rw [he]
  linarith
 theorem blockEvent_conditional_lower (hp : 2≤p) (hd : 0<d) {t v : ℝ} (ht : 0<t)
    (hv : 1≤v) (htv : t≤v) (hpt : 256*t≤p)
    (a : MatrixCoordinates (p+1) d) (ha : ‖a‖≤2*Real.sqrt ((p:ℝ)*d))
    (hab : ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖) :
    ENNReal.ofReal (1/2:ℝ) ≤ (normalLaw (t/d)) {g | a+g∈blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))} := by
  classical
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hpd : 0<(p:ℝ)*d := mul_pos (by linarith) hd'
  have hvpd : 0<v*p*d := by positivity
  have htd : 0<t/(d:ℝ) := div_pos ht hd'
  have : IsProbabilityMeasure (normalLaw (ι := MatrixIndex (p+1) d) (t/d)) := normalLaw_probability htd
  obtain ⟨f,hf,U,hU⟩ := hab
  let E : Set (MatrixCoordinates (p+1) d) := {g | a+g∈blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))}
  let N : Set (MatrixCoordinates (p+1) d) := {g | 2*Real.sqrt (v*p*d)≤‖g‖}
  let B : Set (MatrixCoordinates (p+1) d) := {g | Real.sqrt ((p:ℝ)*d)/4≤‖coordinateMask (blockMask f) (rotateCoordinates U g)‖}
  have hN : (normalLaw (t/d)) N≤ENNReal.ofReal (3/8:ℝ) := by
    apply (normalLaw_norm_markov htd (by positivity : 0<2*Real.sqrt (v*p*d))).trans
    apply ENNReal.ofReal_le_ofReal
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,Real.sq_sqrt hvpd.le]
    apply (div_le_iff₀ (by positivity : 0<(2:ℝ)^2*(v*p*d))).mpr
    field_simp
    nlinarith
  have hB : (normalLaw (t/d)) B≤ENNReal.ofReal (1/8:ℝ) := by
    apply (normalLaw_rotated_mask_markov htd (div_pos (Real.sqrt_pos.mpr hpd) (by norm_num)) f U).trans
    apply ENNReal.ofReal_le_ofReal
    have hc : ((blockMask f).card:ℝ)≤2*(d:ℝ)^2 := by exact_mod_cast blockMask_card_le f hf
    rw [div_pow,Real.sq_sqrt hpd.le]
    apply (div_le_iff₀ (by positivity : 0<(p:ℝ)*d/(4:ℝ)^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hc htd.le
    have he : t/(d:ℝ)*(2*d^2)=2*t*d := by field_simp
    rw [he] at hh
    have hpdt := mul_le_mul_of_nonneg_right hpt hd'.le
    nlinarith
  have hsub : Eᶜ⊆N∪B := by
    intro g hg
    by_contra h
    have hn : ‖g‖<2*Real.sqrt (v*p*d) := lt_of_not_ge (fun hh => h (Or.inl hh))
    have hb : ‖coordinateMask (blockMask f) (rotateCoordinates U g)‖<Real.sqrt ((p:ℝ)*d)/4 :=
      lt_of_not_ge (fun hh => h (Or.inr hh))
    apply hg
    apply blockEvent_add_mem (A := 2*Real.sqrt ((p:ℝ)*d)) (B := 2*Real.sqrt (v*p*d)) _ a g ha hn.le f hf U _ hb.le
    · have hh : Real.sqrt ((p:ℝ)*d)≤Real.sqrt (v*p*d) := Real.sqrt_le_sqrt (by nlinarith)
      linarith
    · linarith
  have hEc : (normalLaw (t/d)) Eᶜ≤ENNReal.ofReal (1/2:ℝ) := by
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans _)
    calc
      _ ≤ ENNReal.ofReal (3/8:ℝ)+ENNReal.ofReal (1/8:ℝ) := add_le_add hN hB
      _ = _ := by rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤3/8) (by norm_num : (0:ℝ)≤1/8)]; congr 1; norm_num
  have hm : MeasurableSet E := (blockEvent_isClosed hd _ _).measurableSet.preimage (by fun_prop : Measurable (fun g : MatrixCoordinates (p+1) d => a+g))
  have hh := measure_add_measure_compl hm (μ := normalLaw (t/d))
  rw [measure_univ] at hh
  have hle : (1:ℝ≥0∞)≤(normalLaw (t/d)) E+ENNReal.ofReal (1/2:ℝ) := by rw [← hh]; exact add_le_add (le_refl _) hEc
  have hfE : (normalLaw (t/d)) E≠⊤ := measure_ne_top _ _
  have htoreal := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hle
  rw [ENNReal.toReal_add hfE (by finiteness)] at htoreal
  change ENNReal.ofReal (1/2:ℝ)≤(normalLaw (t/d)) E
  apply (ENNReal.ofReal_le_iff_le_toReal hfE).mpr
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/2)] at htoreal
  linarith
end FiniteEntropySeparation

end

end OAI
