import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.OrderZeroContractiveCut
import OAI.Analysis.JiangSu.CentralSequences.CentralSequenceSigmaIdeal
import OAI.Analysis.JiangSu.Nuclearity.MatrixKrausLift

namespace OAI

noncomputable section

namespace CompletelyPositiveOperations

open scoped CStarAlgebra ComplexOrder

variable {B E D : Type*} [CStarAlgebra B] [CStarAlgebra E] [CStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder E] [StarOrderedRing E]
  [PartialOrder D] [StarOrderedRing D] [TopologicalSpace.SeparableSpace B]

omit [PartialOrder D] [StarOrderedRing D] in
theorem sigma_order_zero_lift (q : E →⋆ₐ[ℂ] D) (π : B →⋆ₐ[ℂ] D) (φ : B →CP E)
    (hφ : ∀ a, q (φ a)=π a)
    (hσ : ∀ (x w : ℕ → E), (∀ m, q (w m)=0) →
      ∃ d : E, q d=0 ∧ 0≤d ∧ d≤1 ∧ (∀ m, d*w m=w m) ∧ (∀ m, x m*d=d*x m)) :
    ∃ ψ : B →CP E, (∀ a, q (ψ a)=π a) ∧
      (∀ a b, ψ a*ψ b=ψ (a*b)*ψ 1) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq B
  let h := φ 1
  let w : ℕ → E := fun m => φ (a (Nat.unpair m).1)*φ (a (Nat.unpair m).2)-
    φ (a (Nat.unpair m).1*a (Nat.unpair m).2)*h
  have hw (m : ℕ) : q (w m)=0 := by
    simp only [w,h,_root_.map_sub,_root_.map_mul,hφ,_root_.map_one,mul_one,sub_self]
  obtain ⟨d,hd,_,hd1,hdw,hdx⟩ := hσ (fun m => φ (a m)) w hw
  have hφc : Continuous φ := by fun_prop
  have hcomm (b : B) : φ b*d=d*φ b := by
    have he := ha.equalizer (hφc.mul continuous_const) (continuous_const.mul hφc) (funext hdx)
    exact congrFun he b
  have hdefect (b c : B) : d*(φ b*φ c-φ (b*c)*h)=φ b*φ c-φ (b*c)*h := by
    have hfirst (i : ℕ) (c : B) : d*(φ (a i)*φ c-φ (a i*c)*h)=φ (a i)*φ c-φ (a i*c)*h := by
      have he := ha.equalizer
        (show Continuous (fun c => d*(φ (a i)*φ c-φ (a i*c)*h)) by fun_prop)
        (show Continuous (fun c => φ (a i)*φ c-φ (a i*c)*h) by fun_prop)
        (funext (fun j => by simpa only [w,Nat.unpair_pair,Function.comp_apply] using hdw (Nat.pair i j)))
      exact congrFun he c
    have he := ha.equalizer
      (show Continuous (fun b => d*(φ b*φ c-φ (b*c)*h)) by fun_prop)
      (show Continuous (fun b => φ b*φ c-φ (b*c)*h) by fun_prop)
      (funext (fun i => hfirst i c))
    exact congrFun he b
  let c := 1-d
  have hcp : 0≤c := sub_nonneg.mpr hd1
  have hcc (b : B) : Commute c (φ b) := by
    change (1-d)*φ b=φ b*(1-d)
    rw [sub_mul,mul_sub,one_mul,mul_one,hcomm b]
  let ψ := comp (conjugate (CFC.sqrt c)) φ
  have hψ (b : B) : ψ b=c*φ b := by
    change star (CFC.sqrt c)*φ b*CFC.sqrt c=c*φ b
    rw [(CFC.sqrt_nonneg c).isSelfAdjoint.star_eq]
    have hr : Commute (CFC.sqrt c) (φ b) := (hcc b).cfcₙ_nnreal NNReal.sqrt
    rw [mul_assoc,←hr.eq,←mul_assoc,CFC.sqrt_mul_sqrt_self c hcp]
  refine ⟨ψ,?_,?_⟩
  · intro b
    rw [hψ,_root_.map_mul,hφ]
    have hqc : q c=1 := by simp only [c,_root_.map_sub,_root_.map_one,hd,sub_zero]
    rw [hqc,one_mul]
  · intro b e
    simp only [hψ]
    have hz : c*(φ b*φ e)=c*(φ (b*e)*h) := by
      have he := hdefect b e
      change (1-d)*(φ b*φ e)=(1-d)*(φ (b*e)*h)
      rw [sub_mul,sub_mul,one_mul,one_mul]
      rw [mul_sub] at he
      linear_combination (norm := noncomm_ring) -he
    calc
      c*φ b*(c*φ e)=c*(c*(φ b*φ e)) := by
        rw [mul_assoc,←mul_assoc (φ b),←(hcc b).eq,mul_assoc]
      _=c*(c*(φ (b*e)*h)) := congrArg (fun z => c*z) hz
      _=c*φ (b*e)*(c*φ 1) := by
        rw [mul_assoc,←mul_assoc (φ (b*e)),←(hcc (b*e)).eq,mul_assoc]

end CompletelyPositiveOperations

namespace NonunitalGamma

open Pureness CurrentMain Filter Topology CompletelyPositiveOperations
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "D" => FamilyUltrapower T U
local notation "F" => CentralSequenceAlgebra (A := A) U
local notation "q" => centralSequenceToTracial (A := A) U

theorem central_matrix_order_zero_lift (n : ℕ) (hn : 0<n)
    (η : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] D)
    (hη : ∀ M a, η M*quotientInclusion U a=quotientInclusion U a*η M) :
    ∃ φ : CStarMatrix (Fin n) (Fin n) ℂ →CP F,
      (∀ M, q (φ M)=η M) ∧ (∀ M, ‖φ M‖≤‖M‖) ∧
      (∀ M N, φ M*φ N=φ (M*N)*φ 1) ∧
      (∀ M N, 0≤M → 0≤N → M*N=0 → φ M*φ N=0) ∧ q (φ 1)=1 := by
  classical
  let : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
      (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  let p : Fin n := ⟨0,hn⟩
  have hv (i : Fin n) : ∃ v : F, q v=η (matrixUnit i p) :=
    (centralSequenceToTracial_range U _).mpr (hη (matrixUnit i p))
  choose v hv using hv
  let ψ := matrixKraus p v
  have hψ : ∀ M, q (ψ M)=η M := matrixKraus_lift q η p v hv
  obtain ⟨θ,hθ,hθrel⟩ := sigma_order_zero_lift q η ψ hψ (centralSequence_trace_kernel_sigma_ideal U)
  obtain ⟨φ,hφ,hφn,hφrel⟩ := order_zero_contractive_cut q η θ hθ hθrel
  refine ⟨φ,hφ,hφn,hφrel,?_,?_⟩
  · intro M N _ _ hMN
    rw [hφrel,hMN,_root_.map_zero,zero_mul]
  · rw [hφ,_root_.map_one]

end NonunitalGamma

end

end OAI
