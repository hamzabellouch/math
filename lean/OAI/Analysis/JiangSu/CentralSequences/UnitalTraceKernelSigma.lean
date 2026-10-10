import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.UnitalNormToTracial
import OAI.Analysis.JiangSu.CentralSequences.NormTraceKernelSigma
import OAI.Analysis.JiangSu.CentralSequences.NormCentralFunctionalCalculus

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "L" => lp (fun _ : ℕ => A) ∞

theorem trace_kernel_sigma_ideal (hfree : (U : Filter ℕ) ≤ atTop)
    (x w : ℕ → N) (hw : ∀ m, normToTracial (A := A) U (w m)=0) :
    ∃ d : N, normToTracial (A := A) U d=0 ∧ 0≤d ∧ ‖d‖≤1 ∧
      (∀ m, d*w m=w m) ∧ (∀ m, x m*d=d*x m) := by
  classical
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0<e n := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlocal (n : ℕ) : ∃ d : N, normToTracial (A := A) U d=0 ∧ 0≤d ∧ ‖d‖≤1 ∧
      (∀ m≤n, ‖w m-d*w m‖≤e n) ∧ (∀ m≤n, ‖x m*d-d*x m‖<e n) := by
    obtain ⟨d,hd,hp,hn,hW,hX⟩ := Quasicentral.exists_quasicentral_kernel_contraction
      (normToTracial (A := A) U) ((Finset.range (n+1)).image x) ((Finset.range (n+1)).image w)
      (by intro v hv; obtain ⟨m,_hm,rfl⟩ := Finset.mem_image.mp hv; exact hw m) (he n)
    exact ⟨d,hd,hp,hn,fun m hm => hW _ (Finset.mem_image.mpr ⟨m,Finset.mem_range.mpr (by omega),rfl⟩),
      fun m hm => hX _ (Finset.mem_image.mpr ⟨m,Finset.mem_range.mpr (by omega),rfl⟩)⟩
  choose d hd hp hn hW hX using hlocal
  choose b hb hbp hbn using fun n => NormUltra.QuotientAlgebra.positive_contraction_representative (hp n) (hn n)
  choose a ha using fun m => NormUltra.QuotientAlgebra.mk_surjective (x m)
  choose c hc using fun m => NormUltra.QuotientAlgebra.mk_surjective (w m)
  have hnull (n : ℕ) : Tendsto (fun k => familyTwoNorm T (b n k))
      (U : Filter ℕ) (𝓝 0) := by
    have hz : (familyNullIdeal T (U : Filter ℕ)).quotientMap (b n)=0 := by
      change normToTracial (A := A) U (NormUltra.QuotientAlgebra.mk U (b n))=0
      rw [hb n,hd n]
    exact (familyQuotientMap_eq_zero T U (b n)).mp hz
  let P : ℕ → ℕ → Prop := fun n k => familyTwoNorm T (b n k)<e n ∧
    ∀ m≤n, ‖c m k-b n k*c m k‖<2*e n ∧ ‖a m k*b n k-b n k*a m k‖<2*e n
  have hP (n : ℕ) : ∀ᶠ k in (U : Filter ℕ), P n k := by
    have hz := (tendsto_order.mp (hnull n)).2 (e n) (he n)
    have herr (m : ℕ) (hm : m≤n) : ∀ᶠ k in (U : Filter ℕ),
        ‖c m k-b n k*c m k‖<2*e n ∧ ‖a m k*b n k-b n k*a m k‖<2*e n := by
      have h1 : ‖NormUltra.QuotientAlgebra.mk U (c m-b n*c m)‖<2*e n := by
        rw [NormUltra.QuotientAlgebra.mk_sub,NormUltra.QuotientAlgebra.mk_mul,hb n,hc m]
        exact (hW n m hm).trans_lt (by linarith [he n])
      have h2 : ‖NormUltra.QuotientAlgebra.mk U (a m*b n-b n*a m)‖<2*e n := by
        rw [NormUltra.QuotientAlgebra.mk_sub,NormUltra.QuotientAlgebra.mk_mul,
          NormUltra.QuotientAlgebra.mk_mul,hb n,ha m]
        exact (hX n m hm).trans (by linarith [he n])
      exact (NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ h1).and (NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ h2)
    have hall := (eventually_all_finset (Finset.range (n+1))).mpr
      (fun m hm => herr m (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hm))
    filter_upwards [hz,hall] with k hk hkall
    exact ⟨hk,fun m hm => hkall m (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨j,hj,hjP⟩ := NonunitalGamma.kernel_diagonal_choice U hfree P hP
  let z : L := ⟨fun k => b (j k) k,memℓp_infty_iff.mpr ⟨1,by
    rintro _ ⟨k,rfl⟩; exact hbn (j k) k⟩⟩
  have hlim : Tendsto (fun k => e (j k)) (U : Filter ℕ) (𝓝 0) := he0.comp hj
  have hznull : normToTracial (A := A) U (NormUltra.QuotientAlgebra.mk U z)=0 := by
    change (familyNullIdeal T (U : Filter ℕ)).quotientMap z=0
    rw [familyQuotientMap_eq_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => familyTwoNorm_nonneg T _) _ hlim
    filter_upwards [hjP] with k hk
    exact hk.1.le
  have hzpos : 0≤NormUltra.QuotientAlgebra.mk U z := by
    let r : L := ⟨fun k => CFC.sqrt (z k),memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨k,rfl⟩
      change ‖CFC.sqrt (b (j k) k)‖≤(1:ℝ)
      rw [CFC.norm_sqrt _ (hbp (j k) k)]
      exact Real.sqrt_le_one.mpr (hbn (j k) k)⟩⟩
    have hr : star r*r=z := by
      apply Subtype.ext
      funext k
      change star (CFC.sqrt (b (j k) k))*CFC.sqrt (b (j k) k)=b (j k) k
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (hbp (j k) k)]
    rw [←hr,NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_star]
    exact star_mul_self_nonneg _
  refine ⟨NormUltra.QuotientAlgebra.mk U z,hznull,hzpos,
    (NormUltra.QuotientAlgebra.norm_mk_le z).trans (lp.norm_le_of_forall_le zero_le_one (fun k => hbn (j k) k)),?_,?_⟩
  · intro m
    have hzero : c m-z*c m∈NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul 2)
      filter_upwards [hjP,hj (eventually_ge_atTop m)] with k hk hmk
      exact (hk.2 m hmk).1.le
    have hz := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (U := U) (c m) (z*c m)).mpr hzero
    rw [NormUltra.QuotientAlgebra.mk_mul,hc m] at hz
    exact hz.symm
  · intro m
    have hzero : a m*z-z*a m∈NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim.const_mul 2)
      filter_upwards [hjP,hj (eventually_ge_atTop m)] with k hk hmk
      exact (hk.2 m hmk).2.le
    have hz := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (U := U) (a m*z) (z*a m)).mpr hzero
    rwa [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_mul,ha m] at hz

end DirectComparison

end
end

section

noncomputable section
namespace NormUltra.QuotientAlgebra
open scoped ENNReal

variable {A : Type*} [CStarAlgebra A] {U : Ultrafilter ℕ}
local notation "N" => QuotientAlgebra (fun _ : ℕ => A) U
instance : One N := ⟨mk U (DirectComparison.boundedDiagonal (1:A))⟩
instance : Ring N where
  one_mul x := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    change mk U (DirectComparison.boundedDiagonal (1:A)*x)=mk U x
    congr 1
    ext n
    exact one_mul (x n)
  mul_one x := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    change mk U (x*DirectComparison.boundedDiagonal (1:A))=mk U x
    congr 1
    ext n
    exact mul_one (x n)
instance : NormedRing N where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le
instance : Algebra ℂ N := Algebra.ofModule smul_mul_assoc mul_smul_comm
instance : NormedAlgebra ℂ N where
  norm_smul_le := norm_smul_le
instance : CStarAlgebra N where

@[simp] lemma diagonal_one : mk U (DirectComparison.boundedDiagonal (1:A))=(1:N) := rfl
end NormUltra.QuotientAlgebra

end
end

end OAI
