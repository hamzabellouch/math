import OAI.NumberTheory.GaussianMoat.InformationTelescope

namespace OAI

universe uOmega uIota uBeta

namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def chosenSplitFactor (p : ℕ) : GaussianInt :=
  if h : p.Prime ∧ p%4=1 then (exists_split_factor h.1 h.2).choose else 0

lemma chosenSplitFactor_spec {p : ℕ} (hp : p.Prime) (hm : p%4=1) :
    Irreducible (chosenSplitFactor p) ∧ (chosenSplitFactor p).norm=(p:ℤ) := by
  rw [chosenSplitFactor,dite_eq_left ⟨hp,hm⟩]
  exact (exists_split_factor hp hm).choose_spec

noncomputable def splitSieveOf (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ p%4=1) : SplitSieve where
  primes := S
  factor := chosenSplitFactor
  prime_mem := fun p hp => (hS p hp).1
  mod_four := fun p hp => (hS p hp).2
  factor_irreducible := fun p hp => (chosenSplitFactor_spec (hS p hp).1 (hS p hp).2).1
  factor_norm := fun p hp => (chosenSplitFactor_spec (hS p hp).1 (hS p hp).2).2

noncomputable def dyadicSieve (j : ℕ) : SplitSieve :=
  splitSieveOf (PrimeLogMass.dyadicBatch j) (fun p hp => by
    have h := (PrimeLogMass.mem_dyadicBatch j p).mp hp
    exact ⟨h.2.2.1,h.2.2.2⟩)

lemma gaussian_norm_log_nonneg (f : GaussianInt) : 0≤Real.log f.norm.natAbs := by
  by_cases h : f.norm.natAbs=0
  · simp only [h,Nat.cast_zero,Real.log_zero,le_refl]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

noncomputable def residueWeight (F : Finset GaussianInt) : ℝ :=
  ∑ f∈F, Real.log f.norm.natAbs

lemma residueWeight_mono {F G : Finset GaussianInt} (h : F⊆G) : residueWeight F≤residueWeight G :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun f _ _ => gaussian_norm_log_nonneg f)

lemma residueWeight_nonneg (F : Finset GaussianInt) : 0≤residueWeight F :=
  Finset.sum_nonneg (fun f _ => gaussian_norm_log_nonneg f)

theorem residue_vector_entropy {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (z : Ω → GaussianInt) (f : ι → GaussianInt) (hf : ∀ i, f i≠0) :
    p.Hf (fun ω i => residueCode (f i) (z ω))≤∑ i, Real.log (f i).norm.natAbs := by
  let (i : ι) : Finite (GaussianInt ⧸ multiples (f i)) := finite_gaussianResidue (hf i)
  let (i : ι) : Fintype (GaussianInt ⧸ multiples (f i)) := Fintype.ofFinite _
  rw [p.Hf_eq_of_fibers _ (fun ω i => gaussianResidue (f i) (z ω))
    (fun ω ν => residueCode_vector_fibers f (z ω) (z ν))]
  have hh := p.Hf_le_log_card_type (fun ω i => gaussianResidue (f i) (z ω))
  rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod] at hh
  · convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card,multiples_index (hf i)]
  · intro i _
    exact_mod_cast Fintype.card_ne_zero

lemma residue_finset_entropy {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (z : Ω → GaussianInt) (F : Finset GaussianInt) (hf : ∀ f∈F, f≠0) :
    p.Hf (fun ω (f : F) => residueCode f.val (z ω))≤residueWeight F := by
  have h := residue_vector_entropy p z (fun f : F => f.val) (fun f => hf f.val f.property)
  exact h.trans_eq (Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun f : GaussianInt => Real.log f.norm.natAbs)).symm

noncomputable def SplitSieve.availableFactors (s : SplitSieve) : Finset GaussianInt :=
  Finset.univ.image (fun i : s.primes × Bool => signedFactor (s.factor i.1.val) i.2)

lemma SplitSieve.signed_mem_available (s : SplitSieve) (i : s.SignedIndex) :
    s.signedFactorAt i∈s.availableFactors := by
  exact Finset.mem_image.mpr ⟨(s.enumeration i.2,i.1 i.2),Finset.mem_univ _,rfl⟩

lemma SplitSieve.available_ne_zero (s : SplitSieve) {f : GaussianInt} (hf : f∈s.availableFactors) :
    f≠0 := by
  obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hf
  intro h
  have hn := (signedFactor_norm (s.factor p.val) b).trans (s.factor_norm p.val p.property)
  rw [h] at hn
  have hp := (s.prime_mem p.val p.property).ne_zero
  apply hp
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm

lemma SplitSieve.available_weight (s : SplitSieve) :
    residueWeight s.availableFactors≤2*∑ p∈s.primes, Real.log (p:ℝ) := by
  have hh := Finset.sum_image_le_of_nonneg (s := (Finset.univ : Finset (s.primes × Bool)))
    (g := fun i : s.primes × Bool => signedFactor (s.factor i.1.val) i.2)
    (f := fun f : GaussianInt => Real.log f.norm.natAbs) (fun f _ => gaussian_norm_log_nonneg f)
  change residueWeight s.availableFactors≤_ at hh
  apply hh.trans_eq
  simp only [Fintype.sum_prod_type,signedFactor_norm]
  simp only [s.factor_norm _ (Subtype.property _),Int.natAbs_natCast]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]
  rw [← Finset.sum_subtype s.primes (fun _ => Iff.rfl) (fun p : ℕ => Real.log (p:ℝ))]
  ring

lemma FinLaw.cIf_finset_union {Ω : Type uOmega} {ι : Type uIota} {β : Type uBeta} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (z : Ω → GaussianInt) (Y : Ω → β)
    (F : Finset GaussianInt) (f : ι → GaussianInt) :
    p.cIf (fun ω (g : ↥(F∪Finset.univ.image f)) => residueCode g.val (z ω)) Y
      (fun ω (g : F) => residueCode g.val (z ω))=
    p.cIf (fun ω i => residueCode (f i) (z ω)) Y
      (fun ω (g : F) => residueCode g.val (z ω)) := by
  rw [p.cIf_comm,p.cIf_comm (fun ω i => residueCode (f i) (z ω))]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun i => ?_⟩
      exact congrFun hU ⟨f i,Finset.mem_union_right F (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun g => ?_⟩
      rcases Finset.mem_union.mp g.property with hg|hg
      · exact congrFun hO ⟨g.val,hg⟩
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hg
        simpa only [hi] using congrFun hU i

end GaussianMoat

end OAI
