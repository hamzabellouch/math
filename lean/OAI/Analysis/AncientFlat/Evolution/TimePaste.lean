import OAI.Analysis.AncientFlat.Evolution.InitialCore
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInitial
open ParabolicInterior
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]
def timeJoin (f g : V × ℝ → E) (p : V × ℝ) : E := if p.2<0 then f p else g p
lemma pdist_zero_left_le (p q : V × ℝ) (hp : p.2≤0) (hq : 0≤q.2) :
    pdist p (p.1,0)≤pdist p q ∧ pdist (p.1,0) q≤pdist p q := by
  have hs : |p.2|≤|p.2-q.2| := by rw [abs_of_nonpos hp,abs_of_nonpos (by linarith : p.2-q.2≤0)]; linarith
  have ht : |q.2|≤|p.2-q.2| := by rw [abs_of_nonneg hq,abs_of_nonpos (by linarith : p.2-q.2≤0)]; linarith
  constructor
  · simpa only [pdist,Prod.fst,Prod.snd,sub_self,norm_zero,sub_zero,zero_add] using
      (Real.rpow_le_rpow (abs_nonneg p.2) hs (by norm_num : (0:ℝ)≤1/4)).trans
        (le_add_of_nonneg_left (norm_nonneg (p.1-q.1)))
  · change ‖p.1-q.1‖+|0-q.2|^((1:ℝ)/4)≤‖p.1-q.1‖+|p.2-q.2|^((1:ℝ)/4)
    simp only [zero_sub,abs_neg]
    exact add_le_add le_rfl (Real.rpow_le_rpow (abs_nonneg _) ht (by norm_num : (0:ℝ)≤1/4))

lemma holder_timeJoin (α K a b : ℝ) (hα : 0≤α) (hK : 0≤K) (ha : a≤0) (hb : 0≤b)
    (Ω : Set V) (f g : V × ℝ → E)
    (hf : HolderBound α {p : V × ℝ | p.1∈Ω ∧ p.2∈Icc a 0} f K)
    (hg : HolderBound α {p : V × ℝ | p.1∈Ω ∧ p.2∈Icc 0 b} g K)
    (he : ∀ x∈Ω, f (x,0)=g (x,0)) :
    HolderBound α {p : V × ℝ | p.1∈Ω ∧ p.2∈Icc a b} (timeJoin f g) (2*K) := by
  have hcross (p q : V × ℝ) (hp : p.1∈Ω ∧ p.2∈Icc a 0)
      (hq : q.1∈Ω ∧ q.2∈Icc 0 b) : ‖f p-g q‖≤2*K*pdist p q^α := by
    have hp0 : (p.1,0)∈{p : V × ℝ | p.1∈Ω ∧ p.2∈Icc a 0} := ⟨hp.1,ha,le_rfl⟩
    have hp0' : (p.1,0)∈{p : V × ℝ | p.1∈Ω ∧ p.2∈Icc 0 b} := ⟨hp.1,le_rfl,hb⟩
    obtain ⟨hd1,hd2⟩ := pdist_zero_left_le p q hp.2.2 hq.2.1
    have H1 := (hf.2 p hp (p.1,0) hp0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (pdist_nonneg _ _) hd1 hα) hK)
    have H2 := (hg.2 (p.1,0) hp0' q hq).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (pdist_nonneg _ _) hd2 hα) hK)
    rw [he p.1 hp.1] at H1
    exact (norm_sub_le_norm_sub_add_norm_sub (f p) (g (p.1,0)) (g q)).trans (by linarith)
  refine ⟨?_,?_⟩
  · intro p hp
    dsimp only [timeJoin]
    split_ifs with ht
    · exact (hf.1 p ⟨hp.1,hp.2.1,ht.le⟩).trans (by linarith)
    · exact (hg.1 p ⟨hp.1,le_of_not_gt ht,hp.2.2⟩).trans (by linarith)
  · intro p hp q hq
    have hk : K*pdist p q^α≤2*K*pdist p q^α :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (pdist_nonneg p q) α)
    by_cases hpt : p.2<0 <;> by_cases hqt : q.2<0
    · simpa only [timeJoin,ite_eq_left hpt,ite_eq_left hqt] using
        (hf.2 p ⟨hp.1,hp.2.1,hpt.le⟩ q ⟨hq.1,hq.2.1,hqt.le⟩).trans hk
    · simpa only [timeJoin,ite_eq_left hpt,ite_eq_right hqt] using
        hcross p q ⟨hp.1,hp.2.1,hpt.le⟩ ⟨hq.1,le_of_not_gt hqt,hq.2.2⟩
    · have H := hcross q p ⟨hq.1,hq.2.1,hqt.le⟩ ⟨hp.1,le_of_not_gt hpt,hp.2.2⟩
      simpa only [timeJoin,ite_eq_right hpt,ite_eq_left hqt,norm_sub_rev,pdist,norm_sub_rev,abs_sub_comm] using H
    · simpa only [timeJoin,ite_eq_right hpt,ite_eq_right hqt] using
        (hg.2 p ⟨hp.1,le_of_not_gt hpt,hp.2.2⟩ q ⟨hq.1,le_of_not_gt hqt,hq.2.2⟩).trans hk
end ParabolicInitial

end

end OAI
