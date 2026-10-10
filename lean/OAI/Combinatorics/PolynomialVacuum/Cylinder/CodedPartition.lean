import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemResize

namespace OAI

namespace PolynomialVacuumCylinder
open Classical Filter PolynomialVacuumAlgebra
open scoped Topology
variable {M : ℕ} [NeZero M]
noncomputable def codedWeight (H : ℕ) (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M) : ℂ :=
  if h : ∃S : ArcSystem (bandSites M H),S.code=s then
    if matchesBoundary (recoverVertical H h.choose.current) inp out then h.choose.weight else 0
  else 0

theorem codedWeight_code {H : ℕ} (S : ArcSystem (bandSites M H)) (inp out : ZMod M → Spin) :
    codedWeight H inp out S.code=if matchesBoundary (recoverVertical H S.current) inp out then S.weight else 0 := by
  have he : ∃R : ArcSystem (bandSites M H),R.code=S.code := ⟨S,rfl⟩
  rw [codedWeight,dite_eq_left he]
  rw [ArcSystem.code_injective he.choose_spec]

theorem codedWeight_zero {H : ℕ} (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M)
    (he : ¬∃S : ArcSystem (bandSites M H),S.code=s) : codedWeight H inp out s=0 := by simp [codedWeight,he]

theorem codedWeight_norm (H : ℕ) (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M) :
    ‖codedWeight H inp out s‖≤arcChoiceMajorant s := by
  by_cases he : ∃S : ArcSystem (bandSites M H),S.code=s
  · obtain ⟨S,rfl⟩:=he
    rw [codedWeight_code]
    split_ifs
    · exact S.norm_weight_code.le
    · simpa using arcChoiceMajorant_nonneg S.code
  · rw [codedWeight_zero inp out s he,norm_zero]
    exact arcChoiceMajorant_nonneg s

theorem codedWeight_sum (H : ℕ) (inp out : ZMod M → Spin) :
    (∑'s,codedWeight H inp out s)=∑S : ArcSystem (bandSites M H),
      if matchesBoundary (recoverVertical H S.current) inp out then S.weight else 0 := by
  rw [tsum_eq_sum (s:=Finset.univ.image (ArcSystem.code (M:=M) (H:=H)))]
  · rw [Finset.sum_image (fun A _ B _ he => ArcSystem.code_injective he)]
    simp only [codedWeight_code]
  · intro s hs
    apply codedWeight_zero
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hs

theorem codedWeight_stable (H J : ℕ) (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M)
    (hH : 2*arcChoiceLength s<H) (hJ : 2*arcChoiceLength s<J) :
    codedWeight H inp out s=codedWeight J inp out s := by
  have one (H J : ℕ) (hH : 2*arcChoiceLength s<H) (hJ : 2*arcChoiceLength s<J)
      (he : ∃S : ArcSystem (bandSites M H),S.code=s) : codedWeight H inp out s=codedWeight J inp out s := by
    obtain ⟨S,rfl⟩:=he
    have hh : arcChoiceLength S.code<H := by omega
    have hj : arcChoiceLength S.code<J := by omega
    let R:=S.resize le_rfl hh hj hH.le hJ.le
    have hc : R.code=S.code := S.resize_code le_rfl hh hj hH.le hJ.le
    conv_rhs => rw [← hc,codedWeight_code]
    rw [codedWeight_code]
    have hm:=S.resize_matches le_rfl hh hj hH.le hJ.le inp out
    change matchesBoundary (recoverVertical J R.current) inp out ↔ matchesBoundary (recoverVertical H S.current) inp out at hm
    rw [hm]
    split_ifs
    · exact (S.resize_weight le_rfl hh hj hH.le hJ.le).symm
    · rfl
  by_cases he : ∃S : ArcSystem (bandSites M H),S.code=s
  · exact one H J hH hJ he
  · by_cases hj : ∃S : ArcSystem (bandSites M J),S.code=s
    · exact (one J H hJ hH hj).symm
    · rw [codedWeight_zero inp out s he,codedWeight_zero inp out s hj]

noncomputable def limitingCodedWeight (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M) : ℂ :=
  codedWeight (2*arcChoiceLength s+1) inp out s
noncomputable def arcLimit (inp out : ZMod M → Spin) : ℂ := ∑'s,limitingCodedWeight inp out s

theorem codedWeight_tendsto (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M) :
    Tendsto (fun H => codedWeight H inp out s) atTop (nhds (limitingCodedWeight inp out s)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (2*arcChoiceLength s)] with H hH
  exact (codedWeight_stable H _ inp out s hH (by omega)).symm

theorem partition_tendsto (inp out : ZMod M → Spin) :
    Tendsto (fun H => ∑S : ArcSystem (bandSites M H),
      if matchesBoundary (recoverVertical H S.current) inp out then S.weight else 0) atTop (nhds (arcLimit inp out)) := by
  have ht:=tendsto_tsum_of_dominated_convergence (arcChoice_summable M)
    (codedWeight_tendsto inp out) (Filter.Eventually.of_forall (fun H => codedWeight_norm H inp out))
  simpa only [codedWeight_sum,arcLimit] using ht
end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open Filter PolynomialVacuumCylinder
open scoped Topology

theorem physicalTransfer_powers_tendsto (N : ℕ) (out inp : Fin (N+1) → Spin) :
    Tendsto (fun H => (physicalTransfer (N+1) zeta^H) out inp) atTop
      (nhds (arcLimit (cylinderState N inp) (cylinderState N out))) := by
  apply (partition_tendsto (cylinderState N inp) (cylinderState N out)).congr'
  filter_upwards [eventually_gt_atTop 0] with H hH
  exact (physicalTransfer_pow_arcs N H hH out inp).symm
end PolynomialVacuumAlgebra

end OAI
