import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
import OAI.NumberTheory.DirichletL.Descent.PhysicalBlockBudget

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def secondCellExponent (Z:ℝ) (d:BlockIndex) (i:Fin 4):ℝ:=Real.logb Z (scales d i)

theorem secondCellExponent_nonneg (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    0≤secondCellExponent Z d i := by
  apply Real.logb_nonneg hZ
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem actual_second_child_label_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (x:MarkedSecondSource ι Jo Jn) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)=
      ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*primeProductNorm p x.second.divisor*
      primeProductNorm p x.second.overlap := by
  have hn(S:Finset ι):(Ideal.absNorm (sourceIdeal p S):ℝ)=primeProductNorm p S:=by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈S,p i)).symm
  change (Ideal.absNorm (Ideal.span {jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} *
      sourceIdeal p x.firstCommon * sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap):ℝ)=_
  simp only [map_mul,Nat.cast_mul,hn,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem actual_cell_child_label_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      4*‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*scales d 1*scales d 2 := by
  have hE:= (cell_ratios p hp source hk d x hx 1).2.le
  have hV:= (cell_ratios p hp source hk d x hx 2).2.le
  have he:primeProductNorm p x.second.divisor≤2*scales d 1:=
    (div_le_iff₀ (dyadScale_pos _)).mp hE
  have hv:primeProductNorm p x.second.overlap≤2*scales d 2:=
    (div_le_iff₀ (dyadScale_pos _)).mp hV
  rw [actual_second_child_label_norm]
  calc
    _ ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*(2*scales d 1)*(2*scales d 2) := by
      have hc0 := (primeProductNorm_pos p hp x.firstCommon).le
      have hv0 := (primeProductNorm_pos p hp x.second.overlap).le
      have hs0 := (dyadScale_pos (d 1)).le
      gcongr
    _ = _ := by ring

theorem actual_cell_child_label_power {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ)
    (Z B j eta:ℝ) (hZ:1<Z) (hbin:2≤Z^eta)
    (hC:primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ:‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      Z^(secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hfour:(4:ℝ)≤Z^(2*eta):=by
    have hh:=mul_le_mul hbin hbin (by norm_num) (Real.rpow_nonneg hz.le _)
    norm_num only [←Real.rpow_add hz,show eta+eta=2*eta by ring] at hh
    exact hh
  apply (actual_cell_child_label_bound p hp source hk d x hx u v).trans
  calc
    _≤Z^(2*eta)*Z^(j+eta)*Z^(B+eta)*scales d 1*scales d 2:=by
      have hc0:0≤primeProductNorm p x.firstCommon:=(primeProductNorm_pos p hp _).le
      have hs1:0≤scales d 1:=(dyadScale_pos _).le
      have hs2:0≤scales d 2:=(dyadScale_pos _).le
      gcongr
    _= _:=by
      rw [←second_cell_scale_rpow Z d 1 hZ,←second_cell_scale_rpow Z d 2 hZ,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      unfold secondFormalLabel
      ring

theorem second_cell_clipping_width (Z X b eta:ℝ) (d:BlockIndex)
    (hZ:1<Z) (hX:0<X) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*X) (hthreshold:b≤Z^(6*eta)) :
    max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d≤6*eta := by
  exact (Real.rpow_le_rpow_left_iff hZ).mp
    ((second_cell_clipping_ratio Z X b d hZ hX hb hsource).2.trans hthreshold)

end SevenEighths.InverseMoment

end

end OAI
