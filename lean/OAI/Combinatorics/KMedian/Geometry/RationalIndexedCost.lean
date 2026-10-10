import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost
import OAI.Combinatorics.KMedian.Geometry.RationalImageCost
import OAI.Combinatorics.KMedian.Optimization.IndexedInstanceLP

namespace OAI


                                           
section
namespace MetricKMedian.Instance
open Finset

 theorem indexed_score (I : Instance) (S : Finset (Fin I.n)) :
    Completion.Rational.score (fun c : Fin I.clients.card => I.distance (I.clients.orderEmbOfFin rfl c)) S
      = rationalCost I S := by
  unfold Completion.Rational.score
  calc
    _ = ∑ c : Fin I.clients.card, rationalNearest I (I.clients.orderEmbOfFin rfl c) S := rfl
    _ = ∑ c : ↥I.clients, rationalNearest I c.val S :=
      (I.clients.orderIsoOfFin rfl).toEquiv.sum_comp (fun c => rationalNearest I c.val S)
    _ = rationalCost I S := sum_coe_sort I.clients (fun c => rationalNearest I c S)

 theorem indexed_score_image (I : Instance) (O : Finset (Fin I.facilities.card)) :
    Completion.Rational.score I.indexedDistance O=
      rationalCost I (O.image (I.facilities.orderEmbOfFin rfl)) := by
  rw [← indexed_score,Completion.Rational.score_image]
  rfl

end MetricKMedian.Instance
end

end OAI
