import OAI.Analysis.AncientFlat.Evolution.PhysicalWindow
import OAI.Analysis.AncientFlat.Regularity.TimeScalarHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma physical_fourth_local (γ α : ℝ) (hα : 0<α) (hα1 : α<1)
    (v : ℝ → C₀(V,ℂ))
    (hw : ∀ a : ℝ, ∃ u : ℝ → C₀(V,ℂ),
      (∀ s∈Ioo (0:ℝ) 1, ContDiff ℝ 4 (fun x => u s x)) ∧
      (∀ s∈Icc (0:ℝ) 1, renormalized γ u s=v (a+s)) ∧
      ∃ H : ℝ, 0≤H ∧
        (∀ s∈Icc (1/4:ℝ) 1, ∀ x, ‖iteratedFDeriv ℝ 4 (fun y => u s y) x‖≤H) ∧
        (∀ s∈Icc (1/4:ℝ) 1, ∀ t∈Icc (1/4:ℝ) 1, ∀ x y,
          ‖iteratedFDeriv ℝ 4 (fun z => u s z) x-iteratedFDeriv ℝ 4 (fun z => u t z) y‖≤
            H*(‖x-y‖^α+|s-t|^(α/4))))
    (p : V × ℝ) (ht : p.2<0) :
    ∃ U : Set (V × ℝ), IsOpen U ∧ p∈U ∧ ∃ C : ℝ, 0≤C ∧
      HolderBound α U (fun q => iteratedFDeriv ℝ 4 (fun x => physical γ v q.2 x) q.1) C := by
  let a := similarityTime p.2-1/2
  obtain ⟨u,hs,he,H,hH,hb,hh⟩ := hw a
  have hnear : {t : ℝ | t<0 ∧ similarityTime t-a∈Ioo (1/4:ℝ) (3/4)}∈𝓝 p.2 := by
    apply Filter.inter_mem (Iio_mem_nhds ht)
    exact ((similarityTime_deriv ht).continuousAt.sub_const a).eventually
      (Ioo_mem_nhds (by dsimp [a]; linarith) (by dsimp [a]; linarith))
  obtain ⟨l,r,hp,hJ,hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hnear
  let J := Icc l r
  let φ := fun t => similarityTime t-a
  have hJφ (t) (ht : t∈J) : φ t∈Ioo (0:ℝ) 1 := by
    have hh := (hsub ht).2
    exact ⟨by dsimp [φ]; linarith [hh.1],by dsimp [φ]; linarith [hh.2]⟩
  have hmap : MapsTo φ J (Icc (1/4:ℝ) 1) := by
    intro t ht
    exact ⟨(hsub ht).2.1.le,by dsimp [φ]; linarith [(hsub ht).2.2]⟩
  have hφ : ContDiffOn ℝ 1 φ J := by
    exact ((contDiffOn_id.neg.log (fun t ht => (neg_pos.mpr (hsub ht).1).ne')).neg).sub contDiffOn_const
  obtain ⟨L,hL⟩ := hφ.exists_lipschitzOnWith (by norm_num) (convex_Icc l r) isCompact_Icc
  let ℓ := Real.exp (a/4)
  have hcomp := separated_time_change α ℓ H hα.le hH (Icc (1/4:ℝ) 1) J φ L hL hmap
    (fun s x => iteratedFDeriv ℝ 4 (fun y => u s y) x) hb hh
  let e := fun t => Real.exp ((1/2-γ)*a+φ t/2)*ℓ^4
  have hec : ContDiffOn ℝ 1 e J :=
    (((contDiffOn_const.add (hφ.div_const 2)).exp).mul contDiffOn_const)
  obtain ⟨A,hA,ha⟩ := time_smooth_holder (V := V) α hα hα1.le J isCompact_Icc (convex_Icc l r) e hec
  have hg := ha.smul hcomp hA.le (by positivity)
  have hscale (t) (ht : t∈J) (x : V) :
      iteratedFDeriv ℝ 4 (fun y => physical γ v t y) x=
        e t • iteratedFDeriv ℝ 4 (fun y => u (φ t) y) (ℓ • x) := by
    have hwe : physical γ v t=physicalWindow γ a u (φ t) := by
      apply physical_eq_window
      simpa only [φ,add_sub_cancel] using he (φ t) ⟨(hJφ t ht).1.le,(hJφ t ht).2.le⟩
    have hfunc : (fun x : V => physical γ v t x)=
        Real.exp ((1/2-γ)*a+φ t/2) • (fun x : V => u (φ t) (ℓ • x)) := by
      funext x
      rw [hwe,physicalWindow_apply]
      simp only [Pi.smul_apply,Complex.real_smul,ℓ]
    have huc := hs (φ t) (hJφ t ht)
    have huc' : ContDiff ℝ 4 (fun x : V => u (φ t) (ℓ • x)) :=
      huc.comp (contDiff_const.smul contDiff_id)
    rw [hfunc,iteratedFDeriv_const_smul_apply huc'.contDiffAt,
      iteratedFDeriv_comp_const_smul ℓ huc,smul_smul]
  let U : Set (V × ℝ) := {q | q.2∈interior J}
  refine ⟨U,isOpen_interior.preimage continuous_snd,?_,2*A*(H*(1+|ℓ|^α+(L:ℝ)^(α/4))),by positivity,?_,?_⟩
  · exact mem_interior_iff_mem_nhds.mpr hJ
  · intro q hq
    dsimp only
    rw [hscale q.2 (interior_subset hq) q.1]
    exact hg.1 q (show q.2∈J from interior_subset hq)
  · intro q hq z hz
    dsimp only
    rw [hscale q.2 (interior_subset hq) q.1,hscale z.2 (interior_subset hz) z.1]
    exact hg.2 q (show q.2∈J from interior_subset hq) z (show z.2∈J from interior_subset hz)
end FlatSimilarity

end

end OAI
