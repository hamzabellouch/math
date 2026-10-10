import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledSynthesisEnvelope
import OAI.Analysis.LipschitzHilbert.Estimates.MultiplierError

namespace OAI

/-! The ordinary-tree freezing error is a summable dyadic error, with
its original angular indicator retained on both terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Arbitrary coordinate multipliers on the actual raw packets. -/
def rawSelectorTreeValue (i : Fin 3)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (y x : ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    WithLp.toLp 2 (fun k => c j l u k * beta j l k * P.raw i j l u k y x)

theorem rawSelectorTreeValue_sub (i : Fin 3)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta gamma : ∀ j, P.labels j → κ → ℂ) (y x : ℝ) :
    P.rawSelectorTreeValue i c beta y x - P.rawSelectorTreeValue i c gamma y x =
      P.rawSelectorTreeValue i c (fun j l k => beta j l k-gamma j l k) y x := by
  ext k
  simp only [rawSelectorTreeValue,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_sub,
    Pi.sub_apply,Finset.sum_sub_distrib,mul_sub,sub_mul]

private theorem tree_raw_envelope (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant *
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
       lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) x y (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [←pow_add]; congr 1; omega
  have hA : 0≤(2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have h := mul_le_mul_of_nonneg_left hs hA
  rw [hp] at h
  exact (P.raw_absolute_envelope i j l u k y x).trans (by
    simpa only [absoluteConstant,actualX,actualZ,snappedSite,mul_assoc] using h)

private theorem tree_transverse_overlap (q : ℕ) (horder : 1+2*q≤P.order)
    (b : ℝ) (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (j : Fin N) (l : P.labels j) (y x : ℝ) :
    polynomialWeight b (2*P.width) q y^2 *
      (∑ u : Item j l,
        lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) ≤
      16^q*(4*Real.pi)^2 := by
  have hY (u : Item j l) : |P.width*(P.snappedSite j l u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j l) (P.originZ j l) (P.length j)
      P.width (P.rowSlope j l) P.width_pos (P.site j l u)
    change |P.actualZ j l u-P.width*(P.snappedSite j l u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j l u).2-P.actualZ j l u|+|P.actualZ j l u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hcenter j l u)
      _ = _ := by ring
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ u : Item j l, 16^q *
        (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
         lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y) := by
      apply Finset.sum_le_sum
      intro u _
      have hx := lineEnvelope_antitone (P.length j*(P.snappedSite j l u).1)
        (P.length j) x (by omega : 1≤P.order)
      have hy := (mul_le_mul_of_nonneg_left
        (lineEnvelope_antitone (P.width*(P.snappedSite j l u).2) P.width y horder)
        (sq_nonneg (polynomialWeight b (2*P.width) q y))).trans
        (polynomialWeight_sq_mul_envelope y (P.width*(P.snappedSite j l u).2)
          b P.width (2*P.width) q 1 P.width_pos (by linarith [P.width_pos])
          (by linarith [P.width_pos]) (hY u))
      calc
        _ = lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
            (polynomialWeight b (2*P.width) q y^2 *
             lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by ring
        _ ≤ lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
            (16^q*lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y) :=
          mul_le_mul hx hy (mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _))
            (lineEnvelope_nonneg _ _ _ _)
        _ = _ := by ring
    _ = 16^q * ∑ u : Item j l,
        lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [zero_add] using injective_tile_lattice_overlap (P.snappedSite j l)
        (P.snappedSite_injective j l) 0 0 (P.length j) P.width x y
        (P.length_pos j).ne' P.width_pos.ne' (by decide : 1≤1) (by decide : 1≤1)) (by positivity)

/-- The source-angle error at a fixed point has summable dyadic size.
The multiplier hypotheses concern the original selectors, not the error. -/
theorem raw_tree_selector_error (q K B : ℕ) (horder : 1+2*q≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (w b t radius Cb M Lip sigma : ℝ)
    (hw : 0<w) (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l u, ‖c j l u‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-(t+P.rowSlope j l)|≤radius*(w/P.length j))
    (hnear : ∀ j l k s, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j)))
    (i : Fin 3) (s y x : ℝ) :
    polynomialWeight b (2*P.width) q y^2 *
      ‖P.rawSelectorTreeValue i c
        (fun j l k => multiplierError (selector j l k) t (w/P.length j) s) y x‖ ≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2*((K+1:ℕ)+4) := by
  classical
  have hC := P.absoluteConstant_pos
  let e := fun j : Fin N => errorSourceProfile 1 (radius+Cb) (w/P.length j) |s-t|
  have he0 (j : Fin N) : 0≤e j := errorSourceProfile_nonneg _ _ _ _
    (div_pos hw (P.length_pos j)) (abs_nonneg _)
  have heSum : (∑ j, e j)≤(K+1:ℕ)+4 := by
    have hd (j : Fin N) : w/P.length j=(w/P.topLength)*(2:ℝ)^j.val := by
      dsimp only [length]
      field_simp [P.topLength_pos.ne']
    simp_rw [e,hd]
    simpa using sum_errorSourceProfile N K (w/P.topLength) 1 (radius+Cb) |s-t|
      (div_pos hw P.topLength_pos) (by norm_num) (abs_nonneg _) (by simpa using hK)
  have herror (j : Fin N) (l : P.labels j) (k : κ) :
      ‖multiplierError (selector j l k) t (w/P.length j) s‖≤(2*M+Lip)*e j := by
    apply multiplierError_bound _ _ _ 1 (radius+Cb) M Lip s
      (div_pos hw (P.length_pos j)) (by norm_num) (by norm_num) hwide hM hLip
      (hbound j l k) (by simpa only [one_mul] using hnear j l k s)
    intro hfar
    by_contra hn
    have hsup := hsupport j l k s hn
    have ht : |s-t|≤|s-(t+P.rowSlope j l)|+|P.rowSlope j l| := by
      have hh := abs_sub_le s (t+P.rowSlope j l) t
      simpa only [add_sub_cancel_left] using hh
    have hh := ht.trans (add_le_add hsup (hslope j l))
    nlinarith
  let env := fun j (l : P.labels j) (u : Item j l) =>
    lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
    lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y
  have henv0 (j) (l : P.labels j) (u : Item j l) : 0≤env j l u :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hterm (j) (l : P.labels j) (u : Item j l) :
      ‖WithLp.toLp 2 (fun k => c j l u k *
        multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖ ≤
      P.absoluteConstant*sigma*(2*M+Lip)*e j*env j l u := by
    have hej := he0 j
    have henvj := henv0 j l u
    have hh := diagonal_packet_norm (c j l u)
      (fun k => multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)
      (show 0≤((2*M+Lip)*e j)*(P.absoluteConstant*env j l u) by positivity)
      (fun k => by
        rw [norm_mul]
        exact mul_le_mul (herror j l k) (P.tree_raw_envelope i j l u k y x)
          (norm_nonneg _) (mul_nonneg (by linarith) (he0 j)))
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (hc j l u)
      (show 0≤((2*M+Lip)*e j)*(P.absoluteConstant*env j l u) by positivity))
    calc
      _ = ‖WithLp.toLp 2 (fun k => c j l u k *
          (multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x))‖ := by
        congr 1
        ext k
        simp only [mul_assoc]
      _ ≤ _ := hh'
      _ = _ := by ring
  have hlabel (j) (l : P.labels j) :
      polynomialWeight b (2*P.width) q y^2 *
        (∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
          multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) ≤
      P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
    have hej := he0 j
    calc
      _ ≤ polynomialWeight b (2*P.width) q y^2 *
          (∑ u : Item j l, P.absoluteConstant*sigma*(2*M+Lip)*e j*env j l u) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => hterm j l u) (sq_nonneg _)
      _ = (P.absoluteConstant*sigma*(2*M+Lip)*e j)*
          (polynomialWeight b (2*P.width) q y^2*∑ u : Item j l, env j l u) := by
        rw [←Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (P.tree_transverse_overlap q horder b hcenter j l y x)
        (by positivity)
  have hscale (j) : polynomialWeight b (2*P.width) q y^2 *
      (∑ l : P.labels j, ∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
        multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) ≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum fun l _ => hlabel j l).trans
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    have hb : (Fintype.card (P.labels j):ℝ)≤B := by
      simpa only [Fintype.card_coe] using (Nat.cast_le.mpr (hcard j) : ((P.labels j).card:ℝ)≤B)
    have hej := he0 j
    have hh := mul_le_mul_of_nonneg_right hb
      (show 0≤P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) by positivity)
    convert hh using 1
    ring
  calc
    _ ≤ polynomialWeight b (2*P.width) q y^2 *
        (∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
          multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _))
    _ ≤ ∑ j, (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hscale j
    _ = ((B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2) * ∑ j, e j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left heSum (by positivity)

/-- The original physical packet sum, before restriction to its common
angular-support set. -/
def physicalTreeSelectorValue (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    WithLp.toLp 2 (fun k => c j l u k * beta j l k * P.physicalPacket t j l u k z)

theorem physicalTreeSelectorValue_eq_raw (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue t c beta z =
      P.rawSelectorTreeValue 0 c beta (z.2-t*z.1) z.1 := by
  have hraw (j) (l : P.labels j) (u : Item j l) (k : κ) :
      P.raw 0 j l u k (z.2-t*z.1) z.1=P.physicalPacket t j l u k z := by
    have hh := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k (z.2-t*z.1) t)
    change _ = P.physicalPacket t j l u k (z.1,z.2-t*z.1+t*z.1) at hh
    simpa only [sub_add_cancel] using hh
  simp only [physicalTreeSelectorValue,rawSelectorTreeValue,hraw]

/-- Both the original sum and its frozen replacement keep the same
angular indicator. No support assertion about the frozen sum is used. -/
theorem physical_tree_freezing_error (q K B : ℕ) (horder : 1+2*q≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (w b t radius Cb M Lip sigma : ℝ)
    (hw : 0<w) (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l u, ‖c j l u‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-(t+P.rowSlope j l)|≤radius*(w/P.length j))
    (hnear : ∀ j l k s, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j)))
    (S : Set ℝ) (s : ℝ) (z : ℝ×ℝ) :
    polynomialWeight b (2*P.width) q (z.2-t*z.1)^2 *
      ‖(if s∈S then P.physicalTreeSelectorValue t c (fun j l k => selector j l k s) z else 0) -
        (if s∈S then P.physicalTreeSelectorValue t c
          (fun j l k => if |s-t|≤w/P.length j then selector j l k t else 0) z else 0)‖ ≤
      if s∈S then (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2*((K+1:ℕ)+4)
      else 0 := by
  classical
  by_cases hS : s∈S
  · simp only [hS,ite_true,physicalTreeSelectorValue_eq_raw,rawSelectorTreeValue_sub]
    exact P.raw_tree_selector_error q K B horder hcard w b t radius Cb M Lip sigma
      hw hM hLip hsigma hwide hK hcenter hslope c hc selector hbound hsupport hnear
      0 s (z.2-t*z.1) z.1
  · simp only [hS,ite_false,sub_self,norm_zero,mul_zero,le_refl]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
