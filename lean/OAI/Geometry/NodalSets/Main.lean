import OAI.Geometry.NodalSets.SmoothLimit.SphereIterationPositiveLimit
import OAI.Geometry.NodalSets.SmoothLimit.SpherePersistentLimitMain

namespace OAI

namespace Yau.Target

theorem yau_nodal_set_upper_bound_counterexample : MainTarget := by
  obtain ⟨r,delta,s,hfreq,b,hb,hnear⟩ := sphere_iteration_positive_limit
  exact sphere_persistent_limit_implies_main s hfreq b hb hnear

end Yau.Target

end OAI
