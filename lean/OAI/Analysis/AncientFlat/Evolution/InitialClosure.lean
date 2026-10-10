import OAI.Analysis.AncientFlat.Evolution.InitialCover
import OAI.Analysis.AncientFlat.Regularity.HolderContinuity

namespace OAI
noncomputable section
open Set Filter Topology
namespace ParabolicInitial
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma holder_close_initial {α R h M C : ℝ} (hα : 0<α) (hh : 0<h)
    (f : V × ℝ → E) (hf : HolderBound α (slab R h) f M)
    (hc : HolderBound α (openSlab R h) f C) : HolderBound α (slab R h) f C := by
  let L := 𝓝[>] (0:ℝ)
  let shift (p : V × ℝ) (s : ℝ) : V × ℝ := (p.1,(1-s)*p.2)
  have hs : ∀ᶠ s : ℝ in L, s∈Ioo (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with s hs hs1
    exact ⟨hs,hs1⟩
  have hm (p : V × ℝ) (hp : p∈slab R h) : ∀ᶠ s : ℝ in L, shift p s∈openSlab R h := by
    filter_upwards [hs] with s hs
    refine ⟨hp.1,mul_nonneg (by linarith [hs.2]) hp.2.1,?_⟩
    dsimp [shift]
    exact (mul_le_mul_of_nonneg_left hp.2.2 (by linarith [hs.2] : 0≤1-s)).trans_lt (by nlinarith [hs.1])
  have ht (p : V × ℝ) : Tendsto (shift p) L (𝓝 p) := by
    have H : Continuous (shift p) := continuous_const.prodMk ((continuous_const.sub continuous_id).mul continuous_const)
    simpa only [shift,sub_zero,one_mul,Prod.eta] using (H.tendsto 0).mono_left
      (nhdsWithin_le_nhds : L≤𝓝 0)
  have hft (p : V × ℝ) (hp : p∈slab R h) : Tendsto (fun s => f (shift p s)) L (𝓝 (f p)) := by
    apply (hf.continuousOn hα p hp).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht p,?_⟩
    filter_upwards [hm p hp] with s hs
    exact ⟨hs.1,hs.2.1,hs.2.2.le⟩
  have hpd (p q : V × ℝ) : Tendsto (fun s => pdist (shift p s) (shift q s)^α) L (𝓝 (pdist p q^α)) := by
    have hx (p : V × ℝ) : Tendsto (fun s => (shift p s).1) L (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp (ht p)
    have hy (p : V × ℝ) : Tendsto (fun s => (shift p s).2) L (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp (ht p)
    exact (((hx p).sub (hx q)).norm.add
      (((hy p).sub (hy q)).abs.rpow_const (Or.inr (by norm_num : (0:ℝ)≤1/4)))).rpow_const (Or.inr hα.le)
  constructor
  · intro p hp
    exact le_of_tendsto (hft p hp).norm (by filter_upwards [hm p hp] with s hs; exact hc.1 _ hs)
  · intro p hp q hq
    apply le_of_tendsto_of_tendsto ((hft p hp).sub (hft q hq)).norm (tendsto_const_nhds.mul (hpd p q))
    filter_upwards [hm p hp,hm q hq] with s hsp hsq
    exact hc.2 _ hsp _ hsq
end ParabolicInitial

end

end OAI
