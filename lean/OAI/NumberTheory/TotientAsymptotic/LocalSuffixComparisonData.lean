import OAI.NumberTheory.TotientAsymptotic.LocalSuffixFamily

namespace OAI

/-! Actual bad suffixes retain the ordered geometric prime coordinates of
their parent tuple, together with an explicit order embedding. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def primeFinalOrderEmbedding {N : ℕ} (n : ℕ) : Fin (N-n) ↪o Fin N where
  toFun j := ⟨n+j.val,by have := j.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp only at he
    omega
  map_rel_iff' := by
    intro i j
    change n+i.val ≤ n+j.val ↔ i.val ≤ j.val
    omega

lemma primeFinal_eq_embedding {N : ℕ} (p : Fin N → ℕ) (n : ℕ) :
    primeFinal p n = p ∘ primeFinalOrderEmbedding n := rfl

theorem local_bad_suffix_geometric_data {c : ℝ} (hc : 0<c)
    (d L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ (i : Fin (m x-H)) (r : ℕ),r ∈ localBadSuffixValues x c d L H i →
        ∃ p : Fin (m x-H) → ℕ,
          r=∏ j,primeFinal p i.val j ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
          StrictAnti p ∧
          (∀ j,(p j).Prime) ∧
          (∀ j : Fin (m x-H-i.val),
            IsNormalPrime (localNormalityScale (m x-i.val)) (primeFinal p i.val j)) ∧
          (∀ j : Fin (m x-H-i.val),
            primePrefixCoord p (primeFinalOrderEmbedding i.val j)=B (primeFinal p i.val j)) := by
  classical
  filter_upwards [head_limited_prime_coordinates hc] with H hcoords
  filter_upwards [hcoords,m_tendsto.eventually (eventually_ge_atTop H)] with x hcoords hm
  intro i r hr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hpreg := (Finset.mem_filter.mp hp).1
  have hd := hcoords _ (Nat.sub_add_cancel hm) p (local_regular_tuples_subset hpreg)
  refine ⟨p,rfl,hd.2.1,prime_coordinates_strictAnti hd.1 hd.2.1.1.2.1,hd.1,?_,?_⟩
  · intro j
    exact local_regular_normality hpreg i (primeFinalOrderEmbedding i.val j)
      (by change i.val ≤ i.val+j.val; omega)
  · intro j
    rfl

end TotientAsymptotic

end

end OAI
