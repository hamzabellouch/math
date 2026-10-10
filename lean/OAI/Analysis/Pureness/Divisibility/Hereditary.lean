import OAI.Analysis.Pureness.Traces.TracialRank
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Tactic.NoncommRing

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sandwichSubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A where
  carrier := Set.range (fun w : A => h * w * h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * h * h * y, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp only [star_mul, hh.star_eq, mul_assoc]⟩

noncomputable def hereditarySubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A :=
  (sandwichSubalgebra h hh).topologicalClosure

def hereditaryCarrier (h : A) : Set A := closure (Set.range (fun w : A => h * w * h))

lemma hereditarySubalgebra_coe (h : A) (hh : 0 ≤ h) :
    (hereditarySubalgebra h hh : Set A) = hereditaryCarrier h := rfl

instance hereditarySubalgebra_closed (h : A) (hh : 0 ≤ h) :
    IsClosed (hereditarySubalgebra h hh : Set A) := isClosed_closure

lemma hereditary_sqrt_mem {h a : A} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (ham : a ∈ hereditaryCarrier h) : CFC.sqrt a ∈ hereditaryCarrier h := by
  change CFC.sqrt a ∈ hereditarySubalgebra h hh
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem Real.sqrt (show a ∈ hereditarySubalgebra h hh from ham)

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) : h ∈ hereditaryCarrier h := by
  have hm : h * h ∈ hereditaryCarrier h := subset_closure ⟨1, by simp⟩
  have hs := hereditary_sqrt_mem hh (by simpa only [hh.star_eq] using star_mul_self_nonneg h) hm
  simpa only [CFC.sqrt_mul_self h hh] using hs

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_sandwich_mem {h x y : A} (z : A)
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier h) :
    x * z * y ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  apply isClosed_closure.mem_of_tendsto ((hux.mul_const z).mul hvy)
  apply Eventually.of_forall
  intro j
  obtain ⟨a, ha⟩ := hu j
  obtain ⟨b, hb⟩ := hv j
  apply subset_closure
  exact ⟨a * h * z * h * b, by simp only [← ha, ← hb, mul_assoc]⟩

lemma sqrt_sandwich_mem_hereditary (h z : A) (hh : 0 ≤ h) :
    CFC.sqrt h * z * CFC.sqrt h ∈ hereditaryCarrier h := by
  have hm := hereditary_sqrt_mem hh hh (self_mem_hereditary h hh)
  exact hereditary_sandwich_mem z hm hm

lemma normalizedRoot_mem_hereditary {h a : A} (hh : 0 ≤ h)
    (ha : a ∈ hereditaryCarrier h) (ha0 : 0 ≤ a) (j : ℕ) :
    normalizedRoot a j ∈ hereditaryCarrier h := by
  change normalizedRoot a j ∈ hereditarySubalgebra h hh
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_def, cfcₙ_nnreal_eq_real _ _ (normalizePositive_nonneg a ha0)]
  apply cfcₙ_mem
  exact (hereditarySubalgebra h hh).smul_mem (‖a‖⁻¹) ha
end CuntzPureness

end OAI
