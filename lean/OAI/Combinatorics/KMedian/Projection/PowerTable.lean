import Mathlib
import OAI.Combinatorics.KMedian.Projection.ProductTable

namespace OAI

section Inline_PCPProjectionPowerTable
namespace MetricKMedian.PCP
open scoped Classical

namespace Nested
noncomputable instance inhabited (A : Type) [Inhabited A] : (n : ℕ)→Inhabited (Nested A n)
  | 0 => inferInstanceAs (Inhabited Unit)
  | n+1 => letI := inhabited A n; inferInstanceAs (Inhabited (A×Nested A n))
end Nested
namespace Compiler
open Binary Binary.Automatic

namespace Ordered
noncomputable def nested {A : Type} (o : Ordered A) : (n : ℕ)→Ordered (Nested A n)
  | 0 => fixed Unit
  | n+1 => o.prod (nested o n)
end Ordered
namespace ProjectionTable
noncomputable def nestedEquiv {U : Type} {m : ℕ} (ue : U≃Fin m) : (n : ℕ)→Nested U n≃Fin (m^n)
  | 0 => (Equiv.ofUnique Unit (Fin 1)).trans (finCongr (pow_zero m).symm)
  | n+1 => ((ue.prodCongr (nestedEquiv ue n)).trans finProdFinEquiv).trans (finCongr (by rw [pow_succ']))
variable {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
noncomputable def power (t : ProjectionTable A B) : (n : ℕ)→ProjectionTable (Nested A n) (Nested B n)
  | 0 => build BiProjection.trivial (Equiv.ofUnique Unit (Fin 1)) (Ordered.fixed Unit) (Ordered.fixed Unit)
  | n+1 => product t (power t n)
lemma poly_power (n : ℕ) : Poly (fun t : ProjectionTable A B=>power t n) := by
  induction n with
  | zero => exact Automatic.Poly.const _
  | succ n ih => exact poly_product.comp (Poly.pair Poly.identity ih)
variable {U V D S : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {m : ℕ} (ue : U≃Fin m) (vo : Ordered V) (so : Ordered S)
omit [Fintype A] [Fintype B] [Inhabited B] [Fintype U] [Fintype V] [Fintype D]
  [Fintype S] [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B] in
lemma power_build (n : ℕ) : power (build G ue vo so) n=
    build (G.power n) (nestedEquiv ue n) (vo.nested n) (so.nested n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change product (build G ue vo so) (power (build G ue vo so) n)=_
    rw [ih,product_build]
    apply Prod.ext
    · simp only [build,pow_succ']
    · rfl
end ProjectionTable
end Compiler
end MetricKMedian.PCP

end Inline_PCPProjectionPowerTable

end OAI
