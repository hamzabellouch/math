import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PureComparisonIdentification

namespace OAI

section
namespace ElementaryPositivity.BiTruncation
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma hahn_negative (F : PowerSeries R) (z : ℤ) (hz : z<0) :
    (HahnSeries.ofPowerSeries ℤ R F).coeff z=0 := by
  rw [HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
  rintro ⟨n,hn⟩
  simp only [Nat.castOrderEmbedding_apply] at hn
  omega
lemma hahn_nonnegative (x : HahnSeries ℤ R) (hx : ∀z<0,x.coeff z=0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk (fun n=>x.coeff (n:ℤ)))=x := by
  apply HahnSeries.ext
  funext z
  rcases le_or_gt 0 z with hz|hz
  · lift z to ℕ using hz with n hn
    rw [HahnSeries.ofPowerSeries_apply_coeff,coeff_mk]
  · rw [hahn_negative _ _ hz,hx z hz]
lemma hahn_shift_commute (t : ℤ) (x : HahnSeries ℤ R) :
    HahnSeries.single t 1*x=x*HahnSeries.single t 1 := by
  apply HahnSeries.ext
  funext z
  simp only [HahnSeries.coeff_single_mul,HahnSeries.coeff_mul_single,one_mul,mul_one]
lemma hahn_shift_series_commute (t : ℤ) (f : PowerSeries (HahnSeries ℤ R)) :
    C (HahnSeries.single t 1)*f=f*C (HahnSeries.single t 1) := by
  apply PowerSeries.ext
  intro d
  rw [coeff_C_mul,coeff_mul_C,hahn_shift_commute]
lemma mul_coeff_congr {A : Type*} [Semiring A] (N : ℕ)
    {f f' g g' : PowerSeries A}
    (hf : ∀n≤N,coeff n f=coeff n f') (hg : ∀n≤N,coeff n g=coeff n g') :
    coeff N (f*g)=coeff N (f'*g') := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega),hg ij.2 (by omega)]
lemma finite_laurent_shift (f : PowerSeries (HahnSeries ℤ R)) (D : ℕ) :
    ∃c : ℤ,∃F : PowerSeries (PowerSeries R),∀d≤D,
      coeff d (C (HahnSeries.single (-c) 1)*f)=
        coeff d (PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) F) := by
  classical
  have HB : BddBelow (Set.range (fun i : Fin (D+1)=>(coeff i.val f).order)) :=
    (Set.finite_range _).bddBelow
  obtain ⟨c,hc⟩:=HB
  let G:=C (HahnSeries.single (-c) 1)*f
  let F : PowerSeries (PowerSeries R):=PowerSeries.mk
    (fun d=>PowerSeries.mk (fun n=>(coeff d G).coeff (n:ℤ)))
  refine ⟨c,F,?_⟩
  intro d hd
  change coeff d G=_
  rw [coeff_map]
  dsimp only [F]
  rw [coeff_mk]
  symm
  apply hahn_nonnegative
  intro z hz
  change (coeff d (C (HahnSeries.single (-c) 1)*f)).coeff z=0
  rw [coeff_C_mul,HahnSeries.coeff_single_mul,one_mul]
  apply HahnSeries.coeff_eq_zero_of_lt_order
  have H:=hc (show (coeff d f).order∈Set.range (fun i : Fin (D+1)=>(coeff i.val f).order)
    from ⟨⟨d,by omega⟩,rfl⟩)
  omega

lemma inner_eventually (f : PowerSeries (HahnSeries ℤ R)) (D : ℕ) (z : ℤ) :
    ∃N : ℕ,∀U W : PowerSeries (PowerSeries R),Through N U 1 → Through N W 1 →
      (coeff D (PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) U*f*
        PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) W)).coeff z=(coeff D f).coeff z := by
  obtain ⟨c,F,hF⟩:=finite_laurent_shift f D
  refine ⟨D+(z-c).toNat,?_⟩
  intro U W hU hW
  let H:=HahnSeries.ofPowerSeries ℤ R
  let S : PowerSeries (HahnSeries ℤ R):=C (HahnSeries.single (-c) 1)
  have HE : coeff D (PowerSeries.map H U*(S*f)*PowerSeries.map H W)=
      coeff D (PowerSeries.map H (U*F*W)) := by
    rw [(PowerSeries.map H).map_mul (U*F) W,(PowerSeries.map H).map_mul U F]
    apply mul_coeff_congr D
    · intro n hn
      apply mul_coeff_congr n (fun _ _=>rfl)
      intro d hd
      exact hF d (hd.trans hn)
    · intro _ _;rfl
  have HS : PowerSeries.map H U*(S*f)*PowerSeries.map H W=
      S*(PowerSeries.map H U*f*PowerSeries.map H W) := by
    calc
      _=(PowerSeries.map H U*S)*f*PowerSeries.map H W := by simp only [mul_assoc]
      _=(S*PowerSeries.map H U)*f*PowerSeries.map H W := by
        rw [hahn_shift_series_commute]
      _=_ := by simp only [mul_assoc]
  rw [HS] at HE
  have HL:=congrArg (fun a : HahnSeries ℤ R=>a.coeff (z-c)) HE
  simp only [S,coeff_C_mul,HahnSeries.coeff_single_mul,one_mul,sub_neg_eq_add,
    sub_add_cancel,coeff_map] at HL
  rw [HL]
  have HF:=congrArg (fun a : HahnSeries ℤ R=>a.coeff (z-c)) (hF D le_rfl)
  simp only [coeff_C_mul,HahnSeries.coeff_single_mul,one_mul,sub_neg_eq_add,
    sub_add_cancel,coeff_map] at HF
  rw [HF]
  rcases le_or_gt 0 (z-c) with hz|hz
  · have hcast : ((z-c).toNat:ℤ)=z-c:=Int.toNat_of_nonneg hz
    rw [←hcast,HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff]
    exact Through.conjugate hU hW F D (z-c).toNat le_rfl
  · exact (hahn_negative _ _ hz).trans (hahn_negative _ _ hz).symm
end
end ElementaryPositivity.BiTruncation

end

end OAI
