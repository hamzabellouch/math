import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentRadial
import OAI.Geometry.HyperbolicGroups.DevelopmentCATZero

namespace OAI

section
noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

namespace LocalGeodesic
variable [CompactSpace X] {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}
lemma developed_catZero : @CATZero (LocalGeodesic o) (intrinsicMetric hr hc g) := by
  apply @catZero_of_localCN_radial (LocalGeodesic o) (intrinsicMetric hr hc g) (developed_isGeodesic hr hc g) (developed_radial hr hc g)
  intro m
  refine ⟨r/32000,by positivity,?_⟩
  intro a b z ha hb hz ham hmb
  change intrinsicDist hr hc g a m<r/32000 at ha
  change intrinsicDist hr hc g b m<r/32000 at hb
  change intrinsicDist hr hc g z m<r/32000 at hz
  have hmz := intrinsicDist_comm hr hc g z m
  have hma := intrinsicDist_comm hr hc g a m
  have hmb' := intrinsicDist_comm hr hc g b m
  have dab : intrinsicDist hr hc g a b<r/8000 := by linarith [intrinsicDist_triangle hr hc g a m b]
  have dza : intrinsicDist hr hc g z a<r/8000 := by linarith [intrinsicDist_triangle hr hc g z m a]
  have dzb : intrinsicDist hr hc g z b<r/8000 := by linarith [intrinsicDist_triangle hr hc g z m b]
  have eam := endpoint_dist_eq_of_short hr hc g (by linarith : intrinsicDist hr hc g a m<r/8000)
  have ebm := endpoint_dist_eq_of_short hr hc g (by linarith : intrinsicDist hr hc g b m<r/8000)
  have ezm := endpoint_dist_eq_of_short hr hc g (by linarith : intrinsicDist hr hc g z m<r/8000)
  have eab := endpoint_dist_eq_of_short hr hc g dab
  have eza := endpoint_dist_eq_of_short hr hc g dza
  have ezb := endpoint_dist_eq_of_short hr hc g dzb
  obtain ⟨U,hU,hCAT⟩ := hc (endpoint m)
  have haU : endpoint a ∈ U := hU (by rw [mem_ball,eam]; linarith)
  have hbU : endpoint b ∈ U := hU (by rw [mem_ball,ebm]; linarith)
  have hzU : endpoint z ∈ U := hU (by rw [mem_ball,ezm]; linarith)
  have hmU : endpoint m ∈ U := hU (mem_ball_self hr)
  have hcn := CATZero.cn_of_dist hCAT (x:=⟨endpoint a,haU⟩) (y:=⟨endpoint b,hbU⟩)
    (p:=⟨endpoint m,hmU⟩) ⟨endpoint z,hzU⟩ (t:=1/2) (by norm_num)
    (by change dist (endpoint a) (endpoint m)=(1/2)*dist (endpoint a) (endpoint b)
        rw [eam,eab]; change intrinsicDist hr hc g a m=intrinsicDist hr hc g a b/2 at ham; linarith)
    (by change dist (endpoint m) (endpoint b)=(1-1/2)*dist (endpoint a) (endpoint b)
        rw [dist_comm,ebm,eab]
        change intrinsicDist hr hc g m b=intrinsicDist hr hc g a b/2 at hmb
        linarith)
  change dist (endpoint z) (endpoint m)^2≤(1-1/2)*dist (endpoint z) (endpoint a)^2+
    (1/2)*dist (endpoint z) (endpoint b)^2-(1/2)*(1-1/2)*dist (endpoint a) (endpoint b)^2 at hcn
  rw [ezm,eza,ezb,eab] at hcn
  change intrinsicDist hr hc g z m^2≤(intrinsicDist hr hc g z a^2+intrinsicDist hr hc g z b^2)/2-intrinsicDist hr hc g a b^2/4
  linarith
end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
