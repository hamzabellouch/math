import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalFiniteEndingData
import OAI.Analysis.Conductivity.Variational.CentralCorrectedRepresentative

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma branchSplicedField_terminal {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) (j : Fin 2)
    {x : Coord3} (hx : z.R≤x 0) :
    branchSplicedField i z j x=centralBasisSlopes j i*x 0+(mFourierCoeff (f j) 0).re := by
  rw [(branchSplicedField_final i z j (by linarith [z.overlap_lt,z.e_pos])).eq_of_nhds]
  exact congrFun (branchFinitePair_terminal i z x hx) j

lemma variableCollarField_terminal_ae {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) (a b : ℝ) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      z.R≤a*(sourceCollarTime y-b) →
      variableCollarField (fun x j => branchSplicedField i z j x) a b y j=
        centralBasisSlopes j i*(a*(sourceCollarTime y-b))+(mFourierCoeff (f j) 0).re := by
  filter_upwards [sourceCollar_open_charts_ae] with y hy hband ht
  obtain ⟨m,n,x,hx,rfl⟩ := hy hband
  rw [variableCollarField_open _ a b m n hx]
  rw [sourceCollarPiece_time_open hx] at ht ⊢
  exact branchSplicedField_terminal i z j ht

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def terminalValue (i : Fin 3) (j : Fin 2) : ℝ :=
  centralBasisSlopes j i*((z.ending i).R+1)+(mFourierCoeff (z.traces i j) 0).re

def terminalTime (i : Fin 3) (y : Coord3) : ℝ :=
  Fin.cases (sourceCollarTime y)
    (fun k => sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) i

def terminalBase (i : Fin 3) : ℝ := if i=0 then centralThickness else -centralThickness

lemma compression_base (i : Fin 3) :
    z.compression i*(-terminalBase i)=(z.ending i).R+1 := by
  unfold compression terminalBase
  split_ifs <;> field_simp [show centralThickness≠0 by norm_num [centralThickness]]

lemma terminal_affine (i : Fin 3) (j : Fin 2) (t : ℝ) :
    centralBasisSlopes j i*(z.compression i*(t-terminalBase i))+
      (mFourierCoeff (z.traces i j) 0).re=
    z.terminalValue i j+centralBasisSlopes j i*z.compression i*t := by
  have hh := z.compression_base i
  dsimp [terminalValue]
  nlinarith [congrArg (fun r => centralBasisSlopes j i*r) hh]

lemma terminal_band_exists : ∃ η : ℝ,0<η ∧ η<centralThickness ∧
    ∀ i : Fin 3,∀ t : ℝ,|t|≤η → (z.ending i).R<z.compression i*(t-terminalBase i) := by
  have hc (i : Fin 3) : ContinuousAt (fun t : ℝ => z.compression i*(t-terminalBase i)) 0 := by fun_prop
  have hn (i : Fin 3) : ∀ᶠ t : ℝ in 𝓝 0,(z.ending i).R<z.compression i*(t-terminalBase i) := by
    apply (hc i).eventually (lt_mem_nhds ?_)
    simpa only [zero_sub,z.compression_base] using (lt_add_one (z.ending i).R)
  have hall : ∀ᶠ t : ℝ in 𝓝 0,∀ i : Fin 3,(z.ending i).R<z.compression i*(t-terminalBase i) :=
    eventually_all.mpr hn
  obtain ⟨ε,hε,hb⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨min (ε/2) (centralThickness/2),lt_min (by positivity) (by norm_num [centralThickness]),
    (min_le_right _ _).trans_lt (by norm_num [centralThickness]),?_⟩
  intro i t ht
  apply hb ?_ i
  change dist t 0<ε
  rw [Real.dist_eq,sub_zero]
  exact (ht.trans (min_le_left _ _)).trans_lt (by linarith)

lemma endRepresentative_terminal_ae (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      (z.ending i).R≤z.compression i*(terminalTime i y-terminalBase i) →
      z.endRepresentative i y j=z.terminalValue i j+
        centralBasisSlopes j i*z.compression i*terminalTime i y := by
  have hh (i : Fin 3) := variableCollarField_terminal_ae i (z.ending i)
    (z.compression i) (terminalBase i) j
  refine Fin.cases ?_ (fun k => ?_) i
  · filter_upwards [hh 0] with y hy he ht
    exact (hy ⟨(show -(1:ℝ)/100≤0 by norm_num).trans he.1,
      he.2.trans (by norm_num [centralThickness])⟩ ht).trans (z.terminal_affine 0 j _)
  · filter_upwards [(sourceChildInverse_quasi (actualChildSign k)).ae (hh k.succ)] with y hy he ht
    exact (hy ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans he.1,
      he.2.trans (by norm_num)⟩ ht).trans (z.terminal_affine k.succ j _)

lemma correctedEndValue_terminal_ae
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      (z.ending i).R≤z.compression i*(terminalTime i y-terminalBase i) →
      z.correctedEndJet j i (WithLp.toLp 2 y) 0=z.terminalValue i j+
        centralBasisSlopes j i*z.compression i*terminalTime i y := by
  filter_upwards [z.endRepresentative_value hs i j,z.endRepresentative_terminal_ae i j]
    with y hv ht hy hT
  exact (hv hy).trans (ht hy hT)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
