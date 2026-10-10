import OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
import OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture
import OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
import OAI.NumberTheory.DirichletL.Descent.SourceDepth

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1<Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

lemma actual_cell_label_nonneg (Z B j eta : ℝ) (d : BlockIndex)
    (hZ : 1<Z) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) :
    0≤actualCellLabelExponent Z B j eta d := by
  have h1 := secondCellExponent_nonneg Z d 1 hZ
  have h2 := secondCellExponent_nonneg Z d 2 hZ
  unfold actualCellLabelExponent secondFormalLabel
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤outerNorms p x i ∧
      outerNorms p x i≤Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

theorem actual_cell_child_total_upper {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z r ell V A B t j eta b : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hb : 1≤b) (hthreshold : b≤Z^(6*eta))
    (hgeom : ∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t))
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d≤(r+3*ell+V)+15*eta := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hgt := actual_second_common_center p hp x (hs.second_divisor x hxs) Z
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD)
  have hj := actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ
  have hd : d∈keys p source := (mem_keys_iff p source d).mpr ⟨x,hx⟩
  have hc := second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hb
    (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  unfold childF decrease actualCellClipping
  linarith

end SevenEighths.InverseMoment
end

end OAI
