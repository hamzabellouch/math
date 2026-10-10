import OAI.Computability.DegreeRigidity.CohenForcing.CohenEffectiveGeneric
import OAI.Computability.DegreeRigidity.CohenForcing.CohenColumnPrefixGeneric
import OAI.Computability.DegreeRigidity.SetModels.ModelRealOperations
import OAI.Computability.DegreeRigidity.Constructibility.RelativeCohenJump

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CountableForcing OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem groundGeneric_iterate_oneGeneric (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (A R : Oracle) (hR : realCode R ∈ M)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)))
    (j : ℕ) : EffectiveCohen.OneGeneric (iterate R j) A :=
  groundGeneric_oneGeneric M hM hT A (iterate R j)
    (sourceT_real_iterate M hM hT hR j) hA

theorem groundGeneric_iterate_join_degree (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (A R : Oracle) (hR : realCode R ∈ M)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)))
    (k : ℕ) : degree (iterate (join A R) k) = degree (join A (iterate R k)) :=
  RelativeCohenJump.iterate_generic_join_degree A R k
    (fun j _ => groundGeneric_iterate_oneGeneric M hM hT A R hR hA j)

theorem selected_column_iterate_join_degree (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (CohenColumnRealName.poset K)))
    (hG : AtomicForcing.GroundGeneric M G) (A R : Oracle) (hR : realCode R ∈ M)
    (hv : (CohenColumnRealName.realName K a).val G.carrier = realCode A) (k : ℕ) :
    degree (iterate (join A R) k) = degree (join A (iterate R k)) :=
  groundGeneric_iterate_join_degree M hM hT A R hR
    (CohenColumnRealName.selected_real_prefix_generic M K a hM hT hK ha G hG A hv) k

end TuringRigidity.InternalCohen

end OAI
