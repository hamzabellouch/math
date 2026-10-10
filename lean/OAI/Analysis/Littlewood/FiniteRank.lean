import OAI.Analysis.Littlewood.Averages

namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

lemma functional_surjective {f : V →ₗ[K] K} (hf : f≠0) : Function.Surjective f := by
  obtain ⟨e,he⟩ : ∃ e, f e≠0 := by
    by_contra h; push Not at h; exact hf (LinearMap.ext h)
  intro a
  refine ⟨(a/f e) • e,?_⟩
  simp [he]

lemma nonparallel_pair_surjective {f g : V →ₗ[K] K} (hf : f≠0)
    (hfg : ∀ c : K, g≠c • f) : Function.Surjective (f.prod g) := by
  obtain ⟨e,he⟩ := functional_surjective hf (1 : K)
  have hk : ∃ y, f y=0 ∧ g y≠0 := by
    by_contra h
    push Not at h
    apply hfg (g e)
    ext x
    have hfx : f (x-f x • e)=0 := by simp [he]
    have hg := h _ hfx
    simp only [map_sub,map_smul,smul_eq_mul] at hg
    change g x=g e*f x
    exact (sub_eq_zero.mp hg).trans (mul_comm _ _)
  obtain ⟨y,hy,hgy⟩ := hk
  rintro ⟨a,b⟩
  refine ⟨a • e + ((b-a*g e)/g y) • y,?_⟩
  ext <;> simp [LinearMap.prod_apply,he,hy,hgy]

lemma pair_surjective_or_proportional {f g : V →ₗ[K] K} (hf : f≠0) :
    Function.Surjective (f.prod g) ∨ ∃ c : K, g=c • f := by
  classical
  by_cases h : ∃ c : K, g=c • f
  · exact Or.inr h
  · exact Or.inl (nonparallel_pair_surjective hf (by simpa using h))

def dotForm {ι : Type uι} [Fintype ι] (a : ι → K) : (ι → K) →ₗ[K] K where
  toFun := dotProduct a
  map_add' := fun x y ↦ dotProduct_add a x y
  map_smul' := fun c x ↦ by simp [dotProduct, Finset.mul_sum, mul_left_comm]

@[simp] lemma dotForm_apply {ι : Type uι} [Fintype ι] (a x : ι → K) :
    dotForm a x=dotProduct a x := rfl

lemma pair_surjective_of_minor {ι : Type uι} [Fintype ι]
    (a b : ι → K) {i j : ι} (h : a i*b j-a j*b i≠0) :
    Function.Surjective ((dotForm a).prod (dotForm b)) := by
  classical
  have ha : dotForm a≠0 := by
    intro hz
    have hai : a i=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hz
    have haj : a j=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hz
    exact h (by simp [hai,haj])
  apply nonparallel_pair_surjective ha
  intro c hc
  have hbi : b i=c*a i := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hc
  have hbj : b j=c*a j := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hc
  apply h
  rw [hbi,hbj]
  ring

lemma exists_nonzero_minor {ι : Type uι} (a b : ι → K)
    (ha : a≠0) (hnp : ∀ c : K, b≠c • a) :
    ∃ i j, a i*b j-a j*b i≠0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, a i≠0 := by
    by_contra h; push Not at h; exact ha (funext h)
  by_contra h
  push Not at h
  apply hnp (b i/a i)
  ext j
  have he := h i j
  change b j=(b i/a i)*a j
  field_simp
  linear_combination he

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

def fiber (f : V → W) (w : W) : Finset V := Finset.univ.filter (fun v ↦ f v=w)

omit [AddGroup V] [AddGroup W] [Fintype W] [DecidableEq V] in
@[simp] lemma mem_fiber {f : V → W} {v : V} {w : W} : v∈fiber f w ↔ f v=w := by
  simp [fiber]

omit [Fintype W] [DecidableEq V] in
lemma fiber_card_eq (f : V →+ W) (hf : Function.Surjective f) (x y : W) :
    (fiber f x).card=(fiber f y).card :=
  AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)

omit [DecidableEq V] in
lemma fiber_card_mul (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    Fintype.card W*(fiber f w).card=Fintype.card V := by
  have hc : Fintype.card V=∑ y : W, (fiber f y).card := by
    simpa only [Finset.card_univ,fiber] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
        (t := (Finset.univ : Finset W)) (f := f) (by simp))
  simp_rw [fiber_card_eq f hf _ w] at hc
  simpa using hc.symm

omit [Fintype W] [DecidableEq V] in
lemma fiber_nonempty (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    (fiber f w).Nonempty := by
  obtain ⟨v,hv⟩ := hf w
  exact ⟨v,by simp [hv]⟩

omit [DecidableEq V] in
lemma fiber_le_card (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    Fintype.card W ≤ Fintype.card V := by
  rw [← fiber_card_mul f hf w]
  exact Nat.le_mul_of_pos_right _ (fiber_nonempty f hf w).card_pos

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [Fintype K] [DecidableEq V] in
lemma joint_fiber_eq (f g : V →ₗ[K] K) (s t : K) :
    (fiber f s).filter (fun v ↦ g v=t) = fiber (f.prod g) (s,t) := by
  ext v
  simp [fiber,Prod.ext_iff]

omit [Fintype K] [DecidableEq V] in
lemma conditional_fiber_card (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t u : K) :
    ((fiber f s).filter (fun v ↦ g v=t)).card =
    ((fiber f s).filter (fun v ↦ g v=u)).card := by
  simp only [joint_fiber_eq]
  exact fiber_card_eq (f.prod g).toAddMonoidHom hfg _ _

omit [DecidableEq V] in
lemma conditional_fiber_count (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s t : K) :
    Fintype.card K*((fiber f s).filter (fun v ↦ g v=t)).card=(fiber f s).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := fiber f s)
    (t := (Finset.univ : Finset K)) (f := g) (by simp)
  simp_rw [conditional_fiber_card f g hfg s _ t] at h
  simpa using h.symm

omit [Fintype K] [DecidableEq V] in
lemma conditional_card_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    ((fiber f s).filter (fun v ↦ g v∈S)).card =
      S.card*((fiber f s).filter (fun v ↦ g v=0)).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (fiber f s).filter (fun v ↦ g v∈S)) (t := S) (f := g)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have he (t : K) (ht : t ∈ S) :
      (((fiber f s).filter (fun v ↦ g v∈S)).filter (fun v ↦ g v=t))=
      ((fiber f s).filter (fun v ↦ g v=t)) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1.1,h.2⟩
    · rintro ⟨hv,hv'⟩; exact ⟨⟨hv,hv' ▸ ht⟩,hv'⟩
  rw [h]
  calc
    _ = ∑ _t ∈ S, ((fiber f s).filter (fun v ↦ g v=0)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [he t ht,conditional_fiber_card f g hfg s t 0]
    _ = _ := by simp

lemma scalar_preimage_card {c : K} (hc : c≠0) (S : Finset K) :
    (Finset.univ.filter (fun s : K ↦ c*s∈S)).card≤S.card := by
  apply Finset.card_le_card_of_injOn (fun s ↦ c*s)
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s hs t ht hst
    exact mul_left_cancel₀ hc hst

omit [DecidableEq V] in
/-- The exceptional centers have a concrete linear bound in the size of the
short-residue set. No joint independence of three or more rows is asserted. -/
lemma exceptional_centers {J : Type uJ} [Fintype J] [DecidableEq J]
    (f : J → V →ₗ[K] K) (hpair : ∀ j l, j≠l → Function.Surjective ((f j).prod (f l)))
    (i : J) (hfi : f i≠0) (S : Finset K) :
    ∃ E : Finset K, E.card≤2*(Fintype.card J)^2*S.card ∧
      ∀ s : K, s∉E → ∀ j l, j≠l → ∀ e : Bool,
      Function.Surjective ((f i).prod (if e then f j+f l else f j-f l)) ∨
      ∃ c : K, (if e then f j+f l else f j-f l)=c • f i ∧ c*s∉S := by
  classical
  let g : (J × J) × Bool → V →ₗ[K] K := fun a ↦
    if a.2 then f a.1.1+f a.1.2 else f a.1.1-f a.1.2
  let E₀ : (J × J) × Bool → Finset K := fun a ↦
    if h : ∃ c : K, c≠0 ∧ g a=c • f i then
      Finset.univ.filter (fun s ↦ h.choose*s∈S) else ∅
  let E := Finset.univ.biUnion E₀
  have hcard (a) : (E₀ a).card≤S.card := by
    dsimp [E₀]
    split_ifs with h
    · exact scalar_preimage_card h.choose_spec.1 S
    · simp
  have hE : E.card≤2*(Fintype.card J)^2*S.card := by
    calc
      _ ≤ ∑ a : (J × J) × Bool, (E₀ a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : (J × J) × Bool, S.card := Finset.sum_le_sum (fun a _ ↦ hcard a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_bool, nsmul_eq_mul, Nat.cast_id]; ring
  refine ⟨E,hE,?_⟩
  intro s hs j l hjl e
  let a : (J × J) × Bool := ((j,l),e)
  have hg : g a≠0 := by
    obtain ⟨v,hv⟩ := hpair j l hjl (1,0)
    have hvj : f j v=1 := congrArg Prod.fst hv
    have hvl : f l v=0 := congrArg Prod.snd hv
    intro hz
    have hz' := congrArg (fun h : V →ₗ[K] K ↦ h v) hz
    cases e <;> simp [g,a,hvj,hvl] at hz'
  rcases pair_surjective_or_proportional (g := g a) hfi with h | ⟨c,hc⟩
  · exact Or.inl h
  · have hc0 : c≠0 := by intro hz; apply hg; simp [hc,hz]
    refine Or.inr ⟨c,hc,?_⟩
    have hex : ∃ d : K, d≠0 ∧ g a=d • f i := ⟨c,hc0,hc⟩
    have hec : hex.choose=c := by
      obtain ⟨v,hv⟩ := functional_surjective hfi 1
      have hh := congrArg (fun h : V →ₗ[K] K ↦ h v) (hex.choose_spec.2.symm.trans hc)
      simpa [hv] using hh
    intro hcs
    apply hs
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    dsimp [E₀]
    rw [dite_eq_left hex]
    simp [hec,hcs]

end PairCounting
section PrimeRanks

lemma int_cast_ne_zero_of_large_prime {q : ℕ} [Fact q.Prime] {z : ℤ}
    (hz : z≠0) (hq : z.natAbs<q) : (z : ZMod q)≠0 := by
  intro h
  have hd : (q : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h
  apply hz
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hq)

lemma pair_surjective_integer_minor {ι : Type uι} [Fintype ι]
    (a b : ι → ℤ) {i j : ι} (h : a i*b j-a j*b i≠0)
    {q : ℕ} [Fact q.Prime] (hq : (a i*b j-a j*b i).natAbs<q) :
    Function.Surjective ((dotForm (fun k ↦ (a k : ZMod q))).prod
      (dotForm (fun k ↦ (b k : ZMod q)))) := by
  apply pair_surjective_of_minor (i := i) (j := j)
  convert int_cast_ne_zero_of_large_prime h hq using 1 ; push_cast ; rfl

/-- The excluded-prime set is replaced by a concrete size threshold; this
suffices because only existence of one sufficiently large prime is needed. -/
lemma integer_rows_eventual_pair_rank {ι : Type uι} {J : Type uJ} [Fintype ι] [Fintype J]
    (a : J → ι → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ)) ≠ 0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ)) ≠ c • (fun k ↦ (a j k : ℚ))) :
    ∃ Q : ℕ, ∀ q : ℕ, ∀ (_hq : Fact q.Prime), Q<q →
      ∀ j l, j≠l → Function.Surjective
        ((dotForm (fun k ↦ (a j k : ZMod q))).prod
         (dotForm (fun k ↦ (a l k : ZMod q)))) := by
  classical
  let Q := ∑ j : J, ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs
  refine ⟨Q,?_⟩
  intro q hq hQ j l hjl
  obtain ⟨k,h,hm⟩ := exists_nonzero_minor (fun k ↦ (a j k : ℚ))
    (fun k ↦ (a l k : ℚ)) (ha j) (hnp j l hjl)
  have hi : a j k*a l h-a j h*a l k≠0 := by
    intro hz
    apply hm
    exact_mod_cast hz
  apply pair_surjective_integer_minor _ _ hi
  apply lt_of_le_of_lt _ hQ
  calc
    _ ≤ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun h : ι ↦ (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    _ ≤ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun k : ι ↦ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun l : J ↦ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)
    _ ≤ Q := by
      dsimp [Q]
      exact Finset.single_le_sum (f := fun j : J ↦ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI
