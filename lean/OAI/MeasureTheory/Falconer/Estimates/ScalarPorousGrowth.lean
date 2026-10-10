import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchedPrefix
import OAI.MeasureTheory.Falconer.Geometry.ScalarBunchNetGain

namespace OAI

/-! Quantitative porous scalar growth after all original-path losses have
 been accounted for. The terminal fibers retain their entire mass. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_porous_log_growth {B C P M : ℕ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    {K K0 κ D : ℝ} (hK : 0 < K) (hK0 : 0 < K0) (hκ : 0 < κ) (hD : 0 < D)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hporous : (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ))
    (hscale : 20*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K0*t^κ*((L.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ))
    (hproj : ∀ t ∈ A, ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
      (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) ≤ D*(L.card:ℝ)) :
    (κ/10)*(P:ℝ)*(M:ℝ)*Real.log 2 ≤ Real.log D := by
  classical
  let T := (scalarPorousLevels M B C k n).card
  obtain ⟨e,he,he0,heT,lo,bs,hchain,_,hprefix,hloss,_,Q,_,_,_,t,ht,hgain⟩ :=
    scalar_actual_cluster_gain hC2 hCB hP L hL hne k n hlevel hK hκ.le hC hB A hA hAb hball
  have hpre := scalar_bunched_prefix_length L hL hne k n hlevel e he he0 heT
    hchain.start_le hprefix hK0 hκ.le hpoint
  have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hco : 0 < κ*(B:ℝ)-2*(P:ℝ) := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTscale : 10*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*(T:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hporous (mul_nonneg hco.le hlog2.le)
    change (κ/2)*(M:ℝ) ≤ (T:ℝ) at hporous
    nlinarith
  have hshort : 10*lo ≤ T := scalar_bunched_prefix_short (by omega) hB hpre hTscale
  let r := (∑ i ∈ Finset.Ico (e T) M, k i)+
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i)).sum
  let s := (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, scalarCompressedBranch e k i)).sum
  let w := ∑ i ∈ Finset.range lo, scalarCompressedBranch e k i
  have hs : (s:ℝ) ≤ (P:ℝ)*((T-lo:ℕ):ℝ)/50 := by
    have hc : (s:ℝ) = (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum := by
      simp only [s,Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_sum]
    rw [hc]
    linarith
  have hw : (w:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ) := by
    simpa only [w,Nat.cast_sum] using hprefix
  have htotal := scalar_uniform_total_card L hL hne (fun i => B*i) k
    (fun _ _ hij => Nat.mul_le_mul_left B hij) (by simp) rfl
    (fun i hi => (hlevel i hi).children_card)
  have hsplit := scalar_total_branch_decomposition hchain e k he.monotone he0 heT
  have hsize : L.card = 2^(r+s+w) := by
    rw [htotal,hsplit]
  rw [← pow_add] at hgain
  change (2:ℝ)^r*Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤ _ at hgain
  have hu := hproj t ht
  rw [hsize,Nat.cast_pow,Nat.cast_ofNat] at hu
  have hnet := scalar_bunch_net_gain hD hchain.start_le hshort hs hw (hgain.trans hu)
  have hh := mul_le_mul_of_nonneg_left hporous (show 0 ≤ (P:ℝ)*Real.log 2/5 by positivity)
  nlinarith

end Falconer.Regularization

end OAI
