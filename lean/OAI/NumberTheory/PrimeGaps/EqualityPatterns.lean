import OAI.NumberTheory.PrimeGaps.TensorProfiles

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem index_density_from_weight_estimates {C : ℝ} (hC : 0<C)
    (W : ℕ → ℕ → ℝ) (a K b M : ℝ)
    (ha : 0<a) (hK : 0<K) (hM : 0<M) (hb : b<a^2/K)
    (hw : ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ioc X (2*X), 0≤W X m)
    (hfirst : ∀ᶠ X : ℕ in atTop,
      a≤average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m))
    (hdetect : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m^2)≤K)
    (hsuppress : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X
        (Finset.Ioc (blockLength (C+1) X) (2*blockLength (C+1) X)) m)≤b)
    (hsecond : ∀ᶠ X : ℕ in atTop, average X (fun m => W X m^2)≤M) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N≥N₀, c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let delta := (a^2/K-b)^2/M
  have hd : 0<delta := div_pos (sq_pos_of_pos (sub_pos.mpr hb)) hM
  let A := 6*(Real.log 4+1)
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<C+1 := by linarith
  refine ⟨delta/(A*(C+1)),div_pos hd (mul_pos hA hL),?_⟩
  apply eventually_atTop.mp
  have hstarts : ∀ᶠ X : ℕ in atTop,
      delta*(X:ℝ)≤((goodStarts X (blockLength (C+1) X)).card:ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hw,hfirst,hdetect,hsuppress,hsecond]
      with X hX hW hF hD hS hQ
    exact goodStarts_bound_of_moments hX (W X) a K b M ha hK hM hb hW hF hD hS hQ
  filter_upwards [eventually_scale_comparison,eventually_ge_atTop 1,
    tendsto_indexScale.eventually (eventually_blockLength_le (C+1) hL),
    tendsto_indexScale.eventually (eventually_blockLength_threshold C hC),
    tendsto_indexScale.eventually hstarts] with N hcompare hN hblock hthreshold hcount
  apply index_bound_of_goodStarts hd hL hA hcompare.1 (by omega)
  · have hdiv := Nat.div_mul_le_self (prime N) 3
    change (prime N/3)*3≤prime N at hdiv
    change 2*indexScale N+blockLength (C+1) (indexScale N)≤prime N
    change (indexScale N)*3≤prime N at hdiv
    omega
  · intro p hp
    have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact hthreshold p (by omega) (by omega)
  · exact hcompare.2
  · exact hcount

def PatternMaps {ι : Type*} (r : Setoid ι) (α : Type*) :=
  {b : ι → α // Setoid.ker b = r}

noncomputable def patternLift {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r → α :=
  Quotient.lift b.val (by
    intro i j hij
    rw [←b.property] at hij
    exact hij)

@[simp] theorem patternLift_mk {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) (i : ι) :
    patternLift b (Quotient.mk r i)=b.val i := rfl

theorem patternLift_injective {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Function.Injective (patternLift b) := by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j =>
      intro h
      apply Quotient.sound
      rw [←b.property]
      exact h

theorem patternLift_map_injective {ι α : Type*} {r : Setoid ι} :
    Function.Injective (@patternLift ι α r) := by
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrFun hab (Quotient.mk r i)

noncomputable def patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) : Finset (ι → α) := Finset.univ.filter (fun b => Setoid.ker b=r)

@[simp] theorem mem_patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (b : ι → α) : b∈patternClass r ↔ Setoid.ker b=r := by
  simp [patternClass]

theorem patternClass_card_le {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    (patternClass (α:=α) r).card ≤ Fintype.card α ^ Fintype.card (Quotient r) := by
  classical
  let e : {b // b∈patternClass (α:=α) r} → (Quotient r → α) :=
    fun b => patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrFun h (Quotient.mk r i)
  have h := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe,Fintype.card_fun] using h

theorem patternClass_pairwise_disjoint {ι α : Type*} [Fintype ι] [Fintype α]
    {r s : Setoid ι} (hrs : r≠s) :
    Disjoint (patternClass (α:=α) r) (patternClass (α:=α) s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hr hs
  exact hrs ((mem_patternClass r b).mp hr |>.symm.trans ((mem_patternClass s b).mp hs))

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

theorem sum_patterns {ι α K : Type*} [Fintype ι] [Fintype α] [AddCommMonoid K]
    (f : (ι → α) → K) :
    (∑ r : Setoid ι, ∑ b∈patternClass (α:=α) r, f b)=∑ b : ι → α, f b := by
  classical
  simp only [patternClass]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

theorem fiberSubsetFamily_image_eq_of_kernel {ι α β : Type*} [Fintype ι]
    (a : ι → α) (b : ι → β) (hab : ∀ i j, a i=a j ↔ b i=b j) :
    fiberSubsetFamily a (Finset.univ.image a)=fiberSubsetFamily b (Finset.univ.image b) := by
  classical
  ext S
  simp only [mem_fiberSubsetFamily_image]
  constructor <;> rintro ⟨hS,h⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mp (h i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mpr (h i hi j hj)⟩

theorem append_fiber_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card=
      (Finset.univ.filter fun i => a i=r).card+(Finset.univ.filter fun i => b i=r).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

theorem append_fiber_card_le_two {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a) (hb : Function.Injective b) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card≤2 := by
  classical
  rw [append_fiber_card]
  have h1 : (Finset.univ.filter fun i => a i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h2 : (Finset.univ.filter fun i => b i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hb ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega

theorem append_left_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a)
    (i : Fin m) (hi : a i∉Set.range b) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n))=
      {i.castAdd n} := by
    ext j
    cases j using Fin.addCases with
    | left j => simp [ha.eq_iff]
    | right j =>
      have hn : b j≠a i := fun h => hi ⟨j,h⟩
      have hne : Fin.natAdd m j≠i.castAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
  rw [he,Finset.card_singleton]

theorem append_right_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (hb : Function.Injective b)
    (i : Fin n) (hi : b i∉Set.range a) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m))=
      {i.natAdd m} := by
    ext j
    cases j using Fin.addCases with
    | left j =>
      have hn : a j≠b i := fun h => hi ⟨j,h⟩
      have hne : j.castAdd n≠Fin.natAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
    | right j => simp [hb.eq_iff]
  rw [he,Finset.card_singleton]

theorem cumulative_tensor_unmatched_kernel_zero {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ positiveSimplex m tau) (hsg : tsupport g ⊆ positiveSimplex n tau)
    {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a≠Set.range b)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (m+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)))=0 := by
  classical
  have hh : ∃ i : Fin (m+n),
      (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b i).card=1 := by
    by_cases hsub : Set.range a⊆Set.range b
    · have hnot : ¬Set.range b⊆Set.range a := fun h => hab (Set.Subset.antisymm hsub h)
      obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hnot
      exact ⟨i.natAdd m,append_right_singleton a b hb i hi⟩
    · obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hsub
      exact ⟨i.castAdd n,append_left_singleton a b ha i hi⟩
  obtain ⟨i,hi⟩ := hh
  exact cumulativeProfile_kernel_singleton_zero (tensorProfile f g)
    (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs)
    (tensorProfile_tsupport f g hsf hsg) (Fin.append a b) _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun r _ => append_fiber_card_le_two a b ha hb r) i hi hF hFs

theorem duplicateLabels_image (n : ℕ) : Finset.univ.image (duplicateLabels n)=Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd n,by simp [duplicateLabels]⟩

theorem duplicate_shiftFamily {n : ℕ} (a : Fin n → ℤ) (ha : Function.Injective a) :
    shiftFamily (Fin.append a a)=fiberSubsetFamily (duplicateLabels n) Finset.univ := by
  have he : Fin.append a a=(fun i => a (duplicateLabels n i)) := by
    funext i
    cases i using Fin.addCases <;> simp [duplicateLabels]
  classical
  conv_rhs => rw [←duplicateLabels_image n]
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  constructor <;> rintro ⟨hS,h⟩
  · refine ⟨hS, fun i hi j hj => ?_⟩
    apply ha
    simpa only [he] using h i hi j hj
  · refine ⟨hS, fun i hi j hj => ?_⟩
    rw [he]
    exact congrArg a (h i hi j hj)

noncomputable def patternEmbedding {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r ↪ α := ⟨patternLift b,patternLift_injective b⟩

noncomputable def embeddingPattern {ι α : Type*} (r : Setoid ι) (e : Quotient r ↪ α) :
    PatternMaps r α := ⟨fun i => e (Quotient.mk r i),by
  apply Setoid.ext
  intro i j
  change e (Quotient.mk r i)=e (Quotient.mk r j) ↔ r i j
  rw [e.injective.eq_iff,Quotient.eq]⟩

noncomputable def patternEquivEmbedding {ι α : Type*} (r : Setoid ι) :
    PatternMaps r α ≃ (Quotient r ↪ α) where
  toFun := patternEmbedding
  invFun := embeddingPattern r
  left_inv b := by apply Subtype.ext; rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    induction x using Quotient.inductionOn with | h i => rfl

noncomputable def patternClassEquiv {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    {b // b∈patternClass (α:=α) r} ≃ (Quotient r ↪ α) :=
  (Equiv.subtypeEquivRight (fun b => mem_patternClass r b)).trans (patternEquivEmbedding r)

theorem patternClass_sum_norm_le {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (f : (ι → α) → ℂ) {E : ℝ} (hE : 0≤E)
    (hf : ∀ b∈patternClass r, ‖f b‖≤E) :
    ‖∑ b∈patternClass r, f b‖≤(Fintype.card α:ℝ)^Fintype.card (Quotient r)*E := by
  classical
  calc
    _ ≤ ∑ _b∈patternClass (α:=α) r, E := norm_sum_le_of_le _ hf
    _ = ((patternClass (α:=α) r).card:ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast patternClass_card_le (α:=α) r) hE

theorem patternClass_scaled_sum_norm_le {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (f g : (ι → α) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (hf : ∀ b∈patternClass r, ‖(L:ℂ)^Fintype.card (Quotient r)*f b-g b‖≤E) :
    ‖(∑ b∈patternClass r, f b)-(∑ b∈patternClass r, g b)/(L:ℂ)^Fintype.card (Quotient r)‖≤
      ((Fintype.card α:ℝ)/L)^Fintype.card (Quotient r)*E := by
  classical
  have h := patternClass_sum_norm_le r (fun b => (L:ℂ)^Fintype.card (Quotient r)*f b-g b) hE hf
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at h
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ b∈patternClass r, f b)-(∑ b∈patternClass r, g b)/(L:ℂ)^Fintype.card (Quotient r) =
      ((L:ℂ)^Fintype.card (Quotient r)*(∑ b∈patternClass r, f b)-∑ b∈patternClass r, g b)/
      (L:ℂ)^Fintype.card (Quotient r) := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans h
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem pattern_errors_tendsto_zero {ι : Type*} [Fintype ι]
    (r : Setoid ι) (H : ℕ → ℕ) (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (ι → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop, 0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ b∈patternClass r,
      ‖(L X:ℂ)^Fintype.card (Quotient r)*f X b-g X b‖≤E X) :
    Tendsto (fun X => (∑ b∈patternClass r, f X b)-
      (∑ b∈patternClass r, g X b)/(L X:ℂ)^Fintype.card (Quotient r)) atTop (𝓝 0) := by
  have hb : ∀ᶠ X in atTop,
      ‖(∑ b∈patternClass r, f X b)-(∑ b∈patternClass r, g X b)/
        (L X:ℂ)^Fintype.card (Quotient r)‖≤
      ((H X:ℝ)/L X)^Fintype.card (Quotient r)*|E X| := by
    filter_upwards [hL,herr] with X hLX hX
    simpa only [Fintype.card_fin] using patternClass_scaled_sum_norm_le r (f X) (g X)
      hLX (abs_nonneg (E X)) (fun b hb => (hX b hb).trans (le_abs_self _))
  apply squeeze_zero_norm' hb
  simpa only [abs_zero,mul_zero] using (hHL.pow (Fintype.card (Quotient r))).mul hE.abs

theorem all_pattern_errors_tendsto_zero {ι : Type*} [Fintype ι]
    (H : ℕ → ℕ) (L : ℕ → ℝ) (lam : ℝ)
    (E : Setoid ι → ℕ → ℝ) (f g : (X : ℕ) → (ι → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop, 0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : ∀ r, Tendsto (E r) atTop (𝓝 0))
    (herr : ∀ r, ∀ᶠ X in atTop, ∀ b∈patternClass r,
      ‖(L X:ℂ)^Fintype.card (Quotient r)*f X b-g X b‖≤E r X) :
    Tendsto (fun X => ∑ r : Setoid ι, ((∑ b∈patternClass r, f X b)-
      (∑ b∈patternClass r, g X b)/(L X:ℂ)^Fintype.card (Quotient r))) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun r _ =>
    pattern_errors_tendsto_zero r H L (E r) lam f g hL hHL (hE r) (herr r))
  simpa only [Finset.sum_const_zero] using h

theorem blockLength_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/Real.log X) atTop (𝓝 lam) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlo : Tendsto (fun X : ℕ => lam-(Real.log (X:ℝ))⁻¹) atTop (𝓝 lam) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := log_pos_of_two_le hX
    apply (le_div_iff₀ hL).mpr
    have hh := (Nat.lt_floor_add_one (lam*Real.log (X:ℝ))).le
    dsimp [blockLength]
    have he : (lam-(Real.log (X:ℝ))⁻¹)*Real.log X=lam*Real.log X-1 := by
      field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact (div_le_iff₀ (log_pos_of_two_le hX)).mpr (blockLength_le_mul_log hlam hX)

theorem blockLength_tendsto {lam : ℝ} (hlam : 0<lam) :
    Tendsto (blockLength lam) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hlam)

theorem blockLength_densityCutoff_eventually {lam : ℝ} (hlam : 0≤lam) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, K*blockLength lam X≤densityCutoff 2 (Real.log X) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop ((K:ℝ)*lam)] with X hX hL
  apply (Nat.le_floor_iff (by positivity : 0≤(Real.log (X:ℝ))^2)).mpr
  push_cast
  have hh := blockLength_le_mul_log hlam hX
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K),
    mul_le_mul_of_nonneg_right hL (log_pos_of_two_le hX).le]

theorem uniform_singularBoxMean_tendsto (s : ℕ) {K : ℕ} (hK : 0<K)
    (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ) (hH : Tendsto H atTop atTop)
    (hdiam : ∀ᶠ X : ℕ in atTop, boxDiameterBound (h:=H X) (a X) (K*H X)) :
    Tendsto (fun X => singularBoxMean (h:=H X) (a X)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h₀,hh₀⟩ := singularBoxMean_uniform s hK hε
  filter_upwards [hH.eventually_ge_atTop h₀,hdiam] with X hX hd
  exact (by simpa only [Real.dist_eq] using hh₀ (H X) hX (a X) hd)

theorem constant_boxDiameterBound {s h : ℕ} (a : ℤ) :
    boxDiameterBound (s:=s) (h:=h) (fun _ => a) h := by
  intro n i j
  dsimp [boxTuple]
  rw [add_sub_add_left_eq_sub]
  have hi := (n i).isLt
  have hj := (n j).isLt
  omega

theorem quotient_ker_card {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α) :
    Fintype.card (Quotient (Setoid.ker b))=(Finset.univ.image b).card := by
  classical
  let f : Quotient (Setoid.ker b) → {a // a∈Finset.univ.image b} := fun x =>
    ⟨Setoid.kerLift b x, by
      induction x using Quotient.inductionOn with | h i => exact Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Setoid.kerLift_injective b
    exact congrArg Subtype.val h
  have hs : Function.Surjective f := by
    rintro ⟨v,hv⟩
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hv
    refine ⟨Quotient.mk _ i,?_⟩
    exact Subtype.ext he
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

noncomputable def numericPattern {ι : Type*} [Fintype ι] (r : Setoid ι) : ι → ℕ :=
  fun i => (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val

theorem numericPattern_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (numericPattern r)=r := by
  apply Setoid.ext
  intro i j
  change (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val=
    (Fintype.equivFin (Quotient r) (Quotient.mk r j)).val ↔ r i j
  rw [Fin.val_inj,(Fintype.equivFin (Quotient r)).injective.eq_iff,Quotient.eq]

theorem constant_boxTuple_injective_iff {s h : ℕ} (a : ℤ) (n : Fin s → Fin h) :
    Function.Injective (boxTuple (fun _ => a) n) ↔ Function.Injective n := by
  constructor
  · intro hn i j he
    apply hn
    simp [boxTuple,he]
  · intro hn i j he
    apply hn
    have hv : (n i:ℕ)=(n j:ℕ) := by
      exact_mod_cast (add_left_cancel he : (n i:ℤ)=(n j:ℤ))
    exact Fin.ext hv

noncomputable def patternTupleEquiv {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    {b // b∈patternClass (α:=Fin h) r} ≃
    {n // n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a)} :=
  (patternClassEquiv r).trans
    ((Equiv.embeddingCongr (Fintype.equivFin (Quotient r)) (Equiv.refl (Fin h))).trans
      ((Equiv.subtypeInjectiveEquivEmbedding _ _).symm.trans
        (Equiv.subtypeEquivRight (fun n => by
          simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and,
            constant_boxTuple_injective_iff]))))

@[simp] theorem patternTupleEquiv_apply {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (j : Fin (Fintype.card (Quotient r))) :
    (patternTupleEquiv r h a b).val j=
      patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
        ((Fintype.equivFin (Quotient r)).symm j) := rfl

theorem patternTupleEquiv_image {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    (Finset.univ.image fun i => a+(b.val i:ℕ))=
      Finset.univ.image (boxTuple (fun _ => a) (patternTupleEquiv r h a b).val) := by
  classical
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨Fintype.equivFin (Quotient r) (Quotient.mk r i),?_⟩
    simp only [boxTuple,patternTupleEquiv_apply,Equiv.symm_apply_apply]
    rfl
  · rintro ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
    refine ⟨i,?_⟩
    simp only [boxTuple,patternTupleEquiv_apply,←hi]
    rfl

end LargePrimeGaps

end OAI
