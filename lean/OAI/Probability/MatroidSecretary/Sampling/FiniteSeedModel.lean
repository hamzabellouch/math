import OAI.Probability.MatroidProphet.Main
import Mathlib.Logic.Equiv.Fintype

namespace OAI

namespace MatroidProphet

/-- A one-hot code retains the entire finite seed, including unused coordinates. -/
noncomputable def finiteSeedEncode (α : Type*) [Fintype α] (a : α) :
    Seed (Fintype.card α) := by
  classical
  exact fun i => decide ((Fintype.equivFin α) a = i)

/-- Total decoding, with an arbitrary fallback on codes outside the encoder range. -/
noncomputable def finiteSeedDecode (α : Type*) [Fintype α] [Nonempty α] :
    Seed (Fintype.card α) → α :=
  Function.invFun (finiteSeedEncode α)

/-- Change only the representation of the complete initial seed. -/
noncomputable def reindexOnlineSeed {n bits bits' : ℕ} (A : OnlineRule n bits)
    (f : Seed bits' → Seed bits) : OnlineRule n bits' where
  decide k r s h := A.decide k (f r) s h
  measurable_decide k := (A.measurable_decide k).comp
    (((measurable_of_finite f).comp measurable_fst).prodMk measurable_snd)

/-- The sacrificed mask and every core decision use the same decoded seed. -/
noncomputable def reindexHiddenSeed {n bits bits' : ℕ} (A : HiddenRule n bits)
    (f : Seed bits' → Seed bits) : HiddenRule n bits' where
  mask r := A.mask (f r)
  core := reindexOnlineSeed A.core f

end MatroidProphet

end OAI
