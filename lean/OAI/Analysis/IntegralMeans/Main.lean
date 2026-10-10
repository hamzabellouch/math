import OAI.Analysis.IntegralMeans.DomainArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

theorem main_theorem : MainStatement := by
  refine ⟨?_,inverse_spectrum_eq_one,?_,?_⟩
  · intro ε hε
    obtain ⟨C,_hC,hbound⟩ := uniform_inverse_square_bound ε hε
    exact ⟨C,hbound⟩
  · intro W hW _hconnected _hsimply _hboundary φ hφ hb s hs hs4
    exact conformal_domain_area hW hφ hb hs hs4
  · intro f hf t ht ht2
    exact univalent_disk_area hf ht ht2

end Brennan

end

end OAI
