import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormTraceKernelSigma
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U

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

end NonunitalSI

end
end

end OAI
