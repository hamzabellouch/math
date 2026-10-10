import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleLocal
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma scaled_extension_energy (D : ℝ) (hD : 0 < D) :
    ∃ J : ℝ, 0 < J ∧ ∀ (L : Finset (Finset Vertex)), HoleFamily L →
      ∀ N : ℕ, 1 ≤ N →
      (∀ z∈box (0,0) (N,N),siteDiameter L z≤N) →
      (∑ e∈incidentEdges (buffer N),(edgeDiameter L e+1:ℝ)^12) ≤ D*(N:ℝ)^2 →
      ∀ u : Vertex → ℝ,
        (N:ℝ)^(-(1/3:ℝ)) * (GridTrace.energy N (3/2) (extension L u))^(2/3:ℝ) ≤
          J*(goodEnergy L N u)^(1/2:ℝ) := by
  classical
  let H : ℝ := 1+128*32^(1/2:ℝ)
  have hH : 0 < H := by dsimp [H];positivity
  let J : ℝ := (2:ℝ)^(2/3:ℝ)*(H^4*D)^(1/6:ℝ)
  refine ⟨J,by dsimp [J];positivity,?_⟩
  intro L hL N hN hd hm u
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  let E := squareEdges N
  let F := localEdges L E
  have hlocal := local_hole_energy L hL N hN u (3/2) (by norm_num) E
    (squareEdges_good N) (squareEdges_endpoints N) hd
  have hFg : ∀ e∈F,goodEdge L e := hlocal.1
  have hFs : F⊆incidentEdges (buffer N) := hlocal.2.1
  have hW (e : Edge) : 1 ≤ holeWeights L (3/2) e ∧
      holeWeights L (3/2) e ≤ H*(edgeDiameter L e+1:ℝ)^3 := by
    have hh := weights_bound L hL (3/2) (by norm_num) e
    norm_num only [show (3/2:ℝ)-1=1/2 by norm_num,show (2:ℝ)*(3/2)=3 by norm_num] at hh
    simpa only [H,add_comm,Real.rpow_natCast,Real.rpow_ofNat] using hh
  have hmom : (∑ e∈F,(holeWeights L (3/2) e)^(4:ℕ)) ≤ (H^4*D)*(N:ℝ)^2 := by
    calc
      _ ≤ ∑ e∈F,H^4*(edgeDiameter L e+1:ℝ)^12 := by
        apply Finset.sum_le_sum
        intro e he
        have hh := pow_le_pow_left₀ (zero_le_one.trans (hW e).1) (hW e).2 4
        simpa only [mul_pow,← pow_mul,show (3:ℕ)*4=12 from rfl] using hh
      _ ≤ ∑ e∈incidentEdges (buffer N),H^4*(edgeDiameter L e+1:ℝ)^12 :=
        Finset.sum_le_sum_of_subset_of_nonneg hFs (fun e he hne => by positivity)
      _ = H^4*(∑ e∈incidentEdges (buffer N),(edgeDiameter L e+1:ℝ)^12) := (Finset.mul_sum _ _ _).symm
      _ ≤ H^4*(D*(N:ℝ)^2) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have hEF : (∑ e∈F,(edgeAbs u e)^2) ≤ goodEnergy L N u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he;exact Finset.mem_filter.mpr ⟨hFs he,hFg e he⟩
    · intro e he hne;exact sq_nonneg _
  have hw := weighted_holder F (fun _ => 1) (holeWeights L (3/2)) (edgeAbs u)
    (fun _ _ => by norm_num) (fun e he => zero_le_one.trans (hW e).1)
    (fun e he => edgeAbs_nonneg u e) (3/2) (by norm_num) (by norm_num)
  norm_num only [one_mul,Real.one_rpow,mul_one,show (1/(3/2):ℝ)=2/3 by norm_num,
    show (2/(2-3/2):ℝ)=4 by norm_num,show ((2-3/2)/(2*(3/2)):ℝ)=1/6 by norm_num,
    Real.rpow_natCast,Real.rpow_ofNat] at hw
  have hsum : 0 ≤ ∑ e∈F,holeWeights L (3/2) e*(edgeAbs u e)^(3/2:ℝ) :=
    Finset.sum_nonneg fun e he => mul_nonneg (zero_le_one.trans (hW e).1) (Real.rpow_nonneg (edgeAbs_nonneg u e) _)
  have hext : GridTrace.energy N (3/2) (extension L u) ≤
      2*∑ e∈F,holeWeights L (3/2) e*(edgeAbs u e)^(3/2:ℝ) :=
    (energy_le_square N (3/2) (extension L u)).trans (mul_le_mul_of_nonneg_left hlocal.2.2 (by norm_num))
  have hroot : (GridTrace.energy N (3/2) (extension L u))^(2/3:ℝ) ≤
      (2:ℝ)^(2/3:ℝ)*(goodEnergy L N u)^(1/2:ℝ)*((H^4*D)*(N:ℝ)^2)^(1/6:ℝ) := by
    calc
      _ ≤ (2*(∑ e∈F,holeWeights L (3/2) e*(edgeAbs u e)^(3/2:ℝ)))^(2/3:ℝ) :=
        Real.rpow_le_rpow (grid_energy_nonneg _ _ _) hext (by norm_num)
      _ = (2:ℝ)^(2/3:ℝ)*(∑ e∈F,holeWeights L (3/2) e*(edgeAbs u e)^(3/2:ℝ))^(2/3:ℝ) :=
        Real.mul_rpow (by norm_num) hsum
      _ ≤ (2:ℝ)^(2/3:ℝ)*((∑ e∈F,(edgeAbs u e)^2)^(1/2:ℝ)*(∑ e∈F,(holeWeights L (3/2) e)^(4:ℕ))^(1/6:ℝ)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ _ := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul
          (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => sq_nonneg _) hEF (by norm_num))
          (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) hmom (by norm_num))
          (by positivity) (Real.rpow_nonneg (goodEnergy_nonneg _ _ _) _)
  have hscale : (N:ℝ)^(-(1/3:ℝ))*((N:ℝ)^2)^(1/6:ℝ)=1 := by
    rw [← Real.rpow_natCast (N:ℝ) 2,← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
    norm_num
  calc
    _ ≤ (N:ℝ)^(-(1/3:ℝ))*((2:ℝ)^(2/3:ℝ)*(goodEnergy L N u)^(1/2:ℝ)*((H^4*D)*(N:ℝ)^2)^(1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = J*(goodEnergy L N u)^(1/2:ℝ) := by
      rw [Real.mul_rpow (by positivity : 0≤H^4*D) (sq_nonneg _)]
      calc
        _ = J*(goodEnergy L N u)^(1/2:ℝ)*((N:ℝ)^(-(1/3:ℝ))*((N:ℝ)^2)^(1/6:ℝ)) := by dsimp [J];ring
        _ = _ := by rw [hscale,mul_one]

end SparseHoles

end

end OAI
