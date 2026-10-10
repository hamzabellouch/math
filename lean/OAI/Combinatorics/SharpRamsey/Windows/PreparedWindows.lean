import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.ExposureWindows

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

abbrev model (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k) :=
  contextual n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t

variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

local instance flat_ActualPreparedWindows_1 : DecidableEq (Block w) := Classical.decEq _

lemma model_owner (z : (model w n k p θ G t).History) (i : (model w n k p θ G t).Index z) :
    (model w n k p θ G t).owner z i=owner w (n+k) ((model w n k p θ G t).origin z i) :=
  atRound_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k)) t z.2 i

lemma model_embedding_owner (z : (model w n k p θ G t).History) (b : Block w)
    (x : Fin ((model w n k p θ G t).remaining z)) :
    (model w n k p θ G t).owner z ((model w n k p θ G t).embedding z (b,x))=some b :=
  atRound_embedding_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k))
    (embedding_owner w (n+k)) t z.2 b x

lemma target_exists (z : (model w n k p θ G t).History) (x : Fin w×Fin (2*(n+k))) :
    ∃ i,(model w n k p θ G t).origin z i=middle w (n+k) x :=
  atRound_unowned n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k))
    (embedding_owner w (n+k)) t z.2 _ (middle_unowned w (n+k) x.1 x.2)

def target (z : (model w n k p θ G t).History) : Fin w×Fin (2*(n+k)) ↪ (model w n k p θ G t).Index z :=
  (model w n k p θ G t).lift z (middle w (n+k)) (target_exists w n k p θ G t z)

lemma target_origin (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).origin z (target w n k p θ G t z (i,x))=middle w (n+k) (i,x) :=
  lift_origin _ _ _ _ _

lemma target_owner (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).owner z (target w n k p θ G t z (i,x))=none := by
  rw [model_owner,target_origin,middle_unowned]

lemma representative_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    (model w n k p θ G t).owner z.1 ((model w n k p θ G t).representative z b)=some b :=
  model_embedding_owner w n k p θ G t z.1 b (z.2 b)

lemma representative_origin_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    owner w (n+k) ((model w n k p θ G t).origin z.1
      ((model w n k p θ G t).representative z b))=some b := by
  rw [←model_owner,representative_owner]

lemma target_between (z : (model w n k p θ G t).FreshHistory) (i : Fin w) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) ∧
    position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true))) := by
  rw [target_origin]
  exact owner_between i _ _ (representative_origin_owner w n k p θ G t z (i,false))
    (representative_origin_owner w n k p θ G t z (i,true)) x

lemma representative_other (z : (model w n k p θ G t).FreshHistory) (b c : Block w) (hbc : b≠c) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      ((model w n k p θ G t).representative z c) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [representative_owner]
  exact fun h=>hbc (Option.some.inj h)

lemma target_other (z : (model w n k p θ G t).FreshHistory) (b : Block w)
    (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      (target w n k p θ G t z.1 (i,x)) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [target_owner]
  exact Option.some_ne_none _

theorem bad_windows_mean (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1)) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((badWindows ((model w n k p θ G t).representative z) (bad z)).card:ℝ))≤
    ∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ) := by
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (((model w n k p θ G t).freshLaw hp).nonneg z)
  have hh := badWindows_card ((model w n k p θ G t).representative z) (bad z)
  rw [representative_selected] at hh
  apply (Nat.cast_le (α:=ℝ)).mpr
  convert! (preTransparency := .all) hh using 1
  congr 1
  ext index
  simp only [mem_inter]

end
end SharpLogRamsey.Selection.Windows

end

end OAI
