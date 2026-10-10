import OAI.Analysis.AncientFlat.Profile.ProfileData

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian Topology
namespace FlatMain
lemma rightD_eq {f : ℝ → ℝ} {y : ℝ} (hy : 0<y) : rightD f y=deriv f y := by
  exact derivWithin_of_mem_nhds (Ici_mem_nhds hy)
lemma rightD_eventually (f : ℝ → ℝ) {y : ℝ} (hy : 0<y) : rightD f=ᶠ[𝓝 y] deriv f := by
  filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
  exact rightD_eq hz
lemma rightT_eq {f : ℝ → ℝ} {y : ℝ} (hy : 0<y) : rightT f y=FlatRadial.T f y := by
  unfold rightT FlatRadial.T
  rw [rightD_eq hy,rightD_eq hy,(rightD_eventually f hy).deriv_eq]
lemma T_congr_nhds {f g : ℝ → ℝ} {y : ℝ} (he : f=ᶠ[𝓝 y] g) : FlatRadial.T f y=FlatRadial.T g y := by
  unfold FlatRadial.T
  rw [he.deriv_eq,he.deriv.deriv_eq]
lemma rightTT_eq {f : ℝ → ℝ} {y : ℝ} (hy : 0<y) : rightT (rightT f) y=FlatRadial.T (FlatRadial.T f) y := by
  rw [rightT_eq hy]
  apply T_congr_nhds
  filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
  exact rightT_eq hz
lemma ProfileData.G_identity (P : ProfileData) {y : ℝ} (hy : 0<y) : P.G y=1+y*P.h y := by
  rw [P.quotient y hy]
  field_simp
  ring
lemma ProfileData.positive (P : ProfileData) {y : ℝ} (hy : 0≤y) : 0<P.G y := by
  obtain ⟨κ,K,hκ,hb⟩ := P.bounds
  exact hκ.trans_le (hb y hy).1
lemma ProfileData.shrinker_positive (P : ProfileData) {t y : ℝ} (ht : t<0) (hy : 0<y) :
    deriv (fun r => FlatRadial.scalarF P.h r y) t+
      (1+y*FlatRadial.scalarF P.h t y)^2*FlatRadial.T (FlatRadial.T (FlatRadial.scalarF P.h t)) y=0 := by
  simpa only [rightTT_eq hy] using P.shrinker t ht y hy.le
lemma ProfileData.originalB_eq (P : ProfileData) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hm : Module.finrank ℝ V=24)
    {t : ℝ} (ht : t<0) (x : V) :
    FlatRadial.originalB P.G P.h t x=ParabolicAnnular.profilePotential P.G (x,t) :=
  FlatRadial.original_potential hm P.G P.h P.smooth P.quotient_smooth
    (fun _y hy => P.G_identity hy) (fun _y hy => P.positive hy)
    (fun _t ht _y hy => P.shrinker_positive ht hy) ht x
end FlatMain

end

end OAI
