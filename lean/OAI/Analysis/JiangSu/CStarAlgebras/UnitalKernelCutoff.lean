import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.UnitalTraceKernelSigma

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U

 omit [TopologicalSpace.SeparableSpace A] in
 @[simp] lemma normToTracial_one : q (1:N)=1 := by
  obtain ⟨x,hx⟩ := normToTracial_surjective (A := A) U 1
  calc
    q (1:N)=q (1:N)*1 := (mul_one _).symm
    _=q (1:N)*q x := by rw [hx]
    _=q ((1:N)*x) := (map_mul q _ _).symm
    _=1 := by rw [one_mul,hx]

 omit [TopologicalSpace.SeparableSpace A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty (TracialState A)] in
 @[simp] lemma normInclusion_one : NonunitalGamma.normInclusion U (1:A)=(1:N) := rfl

 theorem trace_kernel_cutoff_finite (hfree : (U : Filter ℕ) ≤ atTop)
    (F : N) {m : ℕ} (r : Fin m → N) (hr : ∀ i,q (r i)=0) :
    ∃ d : N,q d=0 ∧ 0≤d ∧ ‖d‖≤1 ∧ (∀ i,d*r i=r i) ∧ Commute d F ∧
      ∀ a : A,Commute d (NonunitalGamma.normInclusion U a) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let x : ℕ → N | 0 => F | n+1 => NonunitalGamma.normInclusion U (a n)
  let w : ℕ → N := fun n => if h : n < m then r ⟨n,h⟩ else 0
  have hw (n : ℕ) : q (w n)=0 := by
    dsimp [w]
    split_ifs with h
    · exact hr _
    · exact map_zero q
  obtain ⟨d,hd,hp,hn,hdr,hdx⟩ := trace_kernel_sigma_ideal U hfree x w hw
  refine ⟨d,hd,hp,hn,?_,(hdx 0).symm,?_⟩
  · intro i
    simpa only [w,dite_eq_left i.isLt] using hdr i
  · have hc1 : Continuous (fun b : A => d*NonunitalGamma.normInclusion U b) := by fun_prop
    have hc2 : Continuous (fun b : A => NonunitalGamma.normInclusion U b*d) := by fun_prop
    have hh := ha.equalizer hc1 hc2 (funext fun n => (hdx (n+1)).symm)
    exact fun b => congrFun hh b

end DirectComparison

end
end

section

noncomputable section
namespace CStarExcision
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 theorem support_monotone {F G s : A} (hF : F≤1) (hGF : G≤F) (hGs : G*s=s) : F*s=s := by
  have hpos : 0≤1-F := sub_nonneg.mpr hF
  have hle : star s*(1-F)*s ≤ star s*(1-G)*s :=
    star_left_conjugate_le_conjugate (sub_le_sub_left hGF 1) s
  have hz : star s*(1-F)*s=0 := le_antisymm (by
    simpa only [mul_sub,sub_mul,mul_one,one_mul,mul_assoc,hGs,sub_self] using hle)
    (star_left_conjugate_nonneg hpos s)
  have hsqr : CFC.sqrt (1-F)*s=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul,(CFC.sqrt_nonneg (1-F)).star_eq,mul_assoc,
      ←mul_assoc (CFC.sqrt (1-F)),CFC.sqrt_mul_sqrt_self (1-F) hpos] using hz
  have hprod := congrArg (fun z => CFC.sqrt (1-F)*z) hsqr
  rw [←mul_assoc,CFC.sqrt_mul_sqrt_self _ hpos,mul_zero] at hprod
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hprod

 theorem cutoff_preserves_bound {F d : A} (hF : 0≤F) (hFn : ‖F‖≤1)
    (hd : 0≤d) (hdn : ‖d‖≤1) (hc : Commute d F) :
    0≤(1-d)*F*(1-d) ∧ ‖(1-d)*F*(1-d)‖≤1 ∧ (1-d)*F*(1-d)≤F := by
  have hd1 : d≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg d hd).mp hdn
  have hx : 0≤1-d := sub_nonneg.mpr hd1
  have hxn : ‖1-d‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr (by simpa using hd)
  have hstar : star (1-d)=1-d := hx.star_eq
  have hpos : 0≤(1-d)*F*(1-d) := by
    simpa only [hstar] using star_left_conjugate_nonneg hF (1-d)
  have hnorm : ‖(1-d)*F*(1-d)‖≤1 := by
    calc
      _≤(‖1-d‖*‖F‖)*‖1-d‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(1*1)*1 := mul_le_mul (mul_le_mul hxn hFn (norm_nonneg _) (by norm_num))
        hxn (norm_nonneg _) (by norm_num)
      _=1 := by norm_num
  have hdd : 0≤d-d*d := by
    have h := Commute.mul_nonneg hd hx ((Commute.one_right d).sub_right (Commute.refl d))
    simpa only [mul_sub,mul_one] using h
  have hdiff : 0≤(d+(d-d*d))*F :=
    Commute.mul_nonneg (add_nonneg hd hdd) hF (hc.add_left (hc.sub_left (hc.mul_left hc)))
  refine ⟨hpos,hnorm,sub_nonneg.mp ?_⟩
  convert hdiff using 1
  have hddf : d*F*d=d*d*F := by rw [mul_assoc,←hc.eq,←mul_assoc]
  calc
    F-(1-d)*F*(1-d)=d*F+F*d-d*F*d := by noncomm_ring
    _=d*F+d*F-d*d*F := by rw [←hc.eq,hddf]
    _=(d+(d-d*d))*F := by noncomm_ring

end CStarExcision

end
end

end OAI
