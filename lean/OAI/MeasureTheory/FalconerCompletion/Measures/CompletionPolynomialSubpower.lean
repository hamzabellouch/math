import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.Shells
import OAI.MeasureTheory.FalconerCompletion.Measures.AssemblyClassLaw
import OAI.MeasureTheory.FalconerCompletion.Shells.MonotoneShellTestDensity

namespace OAI

/-! Measures and the conditional distance-set completion. -/

open _root_.OAI.PlanarFalconer

section

namespace CurrentFalconer.AssemblyCompletion
open Filter
open scoped Topology

lemma completion_polynomial_subpower (k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, C*(N:ℝ)^k ≤ ((2:ℝ)^N)^ε := by
  have hr : 1<(2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hr).const_mul C
  have hh : ∀ᶠ N : ℕ in atTop, C*((N:ℝ)^k/((2:ℝ)^ε)^N) ≤ 1 := by
    exact (ht.eventually_lt_const (show C*0<(1:ℝ) by simp)).mono (fun _ h => h.le)
  filter_upwards [hh] with N hN
  have he : ((2:ℝ)^ε)^N=((2:ℝ)^N)^ε := by
    rw [←Real.rpow_natCast ((2:ℝ)^ε) N,←Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ←Real.rpow_natCast (2:ℝ) N,←Real.rpow_mul (by norm_num : (0:ℝ)≤2),mul_comm ε]
  rw [←mul_div_assoc] at hN
  exact ((div_le_one (by positivity)).mp hN).trans_eq he
noncomputable def completionPoly (n p N : ℕ) : ℝ := (((n+3)*N+1)^p:ℕ)
noncomputable def completionError (n p N : ℕ) (sig c C δ : ℝ) : ℝ :=
  δ^(-(n:ℝ)/2)*(2*(((2:ℝ)^N)^(-2:ℝ)+completionPoly n p N*((2:ℝ)^N)^(-sig))+
    C*((2:ℝ)^N)^(-c)+2*completionPoly n p N*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig))
lemma completionError_nonneg (n p N : ℕ) (sig c C δ : ℝ) (hC : 0≤C) (hδ : 0<δ) :
    0≤completionError n p N sig c C δ := by unfold completionError completionPoly; positivity
lemma completionError_decay (n p : ℕ) (sig c C δ : ℝ) (hsig : 0<sig) (hc : 0<c)
    (hC : 0≤C) (hδ : 0<δ) :
    ∃ η A : ℝ, 0<η ∧ 0≤A ∧ ∀ᶠ N : ℕ in atTop,
      completionError n p N sig c C δ ≤ A*(2:ℝ)^(-η*(N:ℝ)) := by
  let η := min 2 (min (sig/2) c)
  refine ⟨η,δ^(-(n:ℝ)/2)*(C+3),by dsimp [η]; positivity,by positivity,?_⟩
  filter_upwards [completion_polynomial_subpower (p+3) (20*(n+4:ℝ)^p) (sig/2) (half_pos hsig),
    eventually_ge_atTop (1:ℕ)] with N hpoly hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hR : (1:ℝ)≤(2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : (0:ℝ)<(2:ℝ)^N := by positivity
  have hP : completionPoly n p N ≤ (n+4:ℝ)^p*(N:ℝ)^p := by
    unfold completionPoly
    push_cast
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have h3 : (N+1:ℝ)^3+2≤10*(N:ℝ)^3 := by
    have ha : (N+1:ℝ)^3≤((2:ℝ)*N)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hb : (1:ℝ)≤(N:ℝ)^3 := one_le_pow₀ hn
    nlinarith
  have hQ : 2*completionPoly n p N*((N+1:ℝ)^3+2)≤((2:ℝ)^N)^(sig/2) := by
    apply le_trans _ hpoly
    calc
      _ ≤ 2*((n+4:ℝ)^p*(N:ℝ)^p)*(10*(N:ℝ)^3) := by gcongr
      _ = 20*(n+4:ℝ)^p*(N:ℝ)^(p+3) := by rw [pow_add];ring
  have hη2 : η≤2 := min_le_left _ _
  have hηs : η ≤ sig/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η≤c := (min_le_right _ _).trans (min_le_right _ _)
  have h2 : ((2:ℝ)^N)^(-2:ℝ)≤((2:ℝ)^N)^(-η) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hcb : ((2:ℝ)^N)^(-c)≤((2:ℝ)^N)^(-η) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hs : 2*completionPoly n p N*((N+1:ℝ)^3+2)*((2:ℝ)^N)^(-sig)≤((2:ℝ)^N)^(-η) := by
    calc
      _ ≤ ((2:ℝ)^N)^(sig/2)*((2:ℝ)^N)^(-sig) := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = ((2:ℝ)^N)^(-(sig/2)) := by rw [←Real.rpow_add hRp];congr 1;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hf : 2*(((2:ℝ)^N)^(-2:ℝ)+completionPoly n p N*((2:ℝ)^N)^(-sig))+
    C*((2:ℝ)^N)^(-c)+2*completionPoly n p N*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)≤
      (C+3)*((2:ℝ)^N)^(-η) := by
    have hcc := mul_le_mul_of_nonneg_left hcb hC
    nlinarith
  unfold completionError
  have hh := mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hδ.le (-(n:ℝ)/2))
  apply hh.trans_eq
  rw [mul_assoc]
  congr 1
  congr 1
  rw [←Real.rpow_natCast (2:ℝ) N,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring
end CurrentFalconer.AssemblyCompletion
end

section

section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ENNReal Classical

theorem assembly_profile_regularization_uniform (d : ℕ) {lam : ℝ} (hlam : 0<lam) :
    ∃ H : ℕ, 0<H ∧ ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ],
      μ (treeCell [])ᶜ=0 → ∀ (s C : ℝ), 0≤C →
      (∀ x : EuclideanSpace ℝ (Fin d), ∀ r>0, μ (ball x r)≤ENNReal.ofReal (C*r^s)) →
      ∃ N₀ : ℕ, ∀ N≥N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves μ N
      let F := regularizationLabel μ N B
      0 < N ∧ 0 < B ∧
      (retainedClassLabels μ N B t).card ≤ ((d+2)*N+1)^(2*H+1) ∧
      μ (retainedClassUnion μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        ((((d+2)*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels μ N B t,
        t ≤ classMeasure μ L F T univ ∧
        ∃ m : ℝ → ℝ, RegularizedProfileData (normalizedClass μ L F T) N B s lam m := by
  classical
  obtain ⟨H,N₁,hH,hHbound,hscales⟩ := exists_bounded_regularization_control hlam
  refine ⟨H,hH,?_⟩
  intro μ _ hcarry s C hC hball
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(d+2:ℝ)^s)
  refine ⟨max H (max N₁ N₂),?_⟩
  intro N hN
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hs := hscales N hN₁
  have hc : (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) ≤ ((d+2)*N+1)^(2*H+1) := by
    rw [pow_succ ((d+2)*N+1) (2*H)]
    apply Nat.mul_le_mul_right
    exact (Nat.pow_le_pow_left (by nlinarith) _).trans (Nat.pow_le_pow_right (by omega) hs.2.2.1)
  refine ⟨hs.1,hs.2.1,(retainedClassLabels_count μ N (N/H) _).trans hc,?_,?_⟩
  · have hh := retainedClass_discard_mass μ hcarry N (N/H)
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    rw [thin_leaf_loss_identity] at hh
    apply hh.trans
    apply add_le_add_right
    apply mul_le_mul_left
    exact_mod_cast hc
  · intro T hT
    refine ⟨retainedClass_mass_lower μ hT,?_⟩
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
    subst T
    refine ⟨sourceProfile μ N (N/H) p,?_⟩
    refine ⟨sourceClass_probability μ N (N/H) hp,
      regularizedProfile_continuous _ _ _ _ _ _,regularizedProfile_zero _ _ _ _ _ _,
      ?_,?_,?_,?_,?_,?_⟩
    · intro u v hu huv hv
      exact regularizedProfile_increment hs.1
        (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
        (regularizationLabel μ N (N/H)) hs.2.1 p hu huv hv
    · exact fun i hi => sourceProfile_affine_on_blocks μ N (N/H) p hi
    · intro n hn P hP hpos
      exact sourceClass_occupied_comparison μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hn hP hpos
    · intro n hn
      refine ⟨?_,sourceProfile_upper μ hs.1 hs.2.1 p (Nat.cast_nonneg n) (Nat.cast_le.mpr hn)⟩
      apply sourceProfile_frostman_lower μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
        (retained_label_real_mass_lower μ hT) _ hn
      intro k hk P hP
      have hh := dyadic_cell_frostman_profile_bound μ hC hball hs.1 P
      rw [hP] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity))
    · exact fun u v hu huN hv hvN => sourceProfile_adjusted_lipschitz μ hs.1 hs.2.1 p hu huN hv hvN
    · exact fun g p' hgp hpN x C₀ hC₀ =>
        sourceClass_local_count μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hgp hpN x hC₀
end GraphLiteralSupport.CurrentFalconer.TreeND
end

section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ENNReal Classical
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
abbrev assemblyRetainedIndex (μ : Measure V) (N B : ℕ) (sig : ℝ) :=
  {T // T∈retainedClassLabels μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-sig)))}
noncomputable def actualAssemblyClassFamily (μ : Measure V) [IsProbabilityMeasure μ]
    (N B : ℕ) (chi sig : ℝ)
    (hp : ∀ T∈retainedClassLabels μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-sig))),
      ∃ m : ℝ → ℝ, RegularizedProfileData
        (normalizedClass μ (regularizationLeaves μ N) (regularizationLabel μ N B) T)
        N B ((n+1:ℝ)/2+chi) sig m) :
    AssemblyClassFamily (assemblyRetainedIndex μ N B sig) μ N B chi sig where
  domain T := leafUnion (classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B) T)
  measurable _ := leafUnion_measurable _
  disjoint := by
    intro T U hne
    apply leafUnion_disjoint (N:=N)
    · exact fun p hp => regularizationLeaves_subset μ N (Finset.mem_filter.mp hp).1
    · exact fun p hp => regularizationLeaves_subset μ N (Finset.mem_filter.mp hp).1
    · exact classLeaves_disjoint _ _ (Subtype.val_injective.ne hne)
  positive T := by
    have h := retainedClass_mass_lower μ T.property
    simp only [classMeasure,Measure.restrict_apply_univ] at h
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) h).ne'
  root T := by
    intro x hx
    obtain ⟨p,_hp,hxp⟩ := mem_iUnion₂.mp hx
    simpa only [List.take_zero] using treeCell_subset_take p 0 hxp
  mass T := Classical.choose (hp T T.property)
  profile T := by
    have h := Classical.choose_spec (hp T T.property)
    simpa only [assemblyClassLaw,normalizedClass,classMeasure,Measure.restrict_apply_univ] using h
lemma actualAssemblyClassFamily_union (μ : Measure V) [IsProbabilityMeasure μ]
    (N B : ℕ) (chi sig : ℝ) (hp) :
    (⋃ T, (actualAssemblyClassFamily μ N B chi sig hp).domain T)=
      retainedClassUnion μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-sig))) := by
  ext x
  simp only [actualAssemblyClassFamily,retainedClassUnion,mem_iUnion]
  constructor
  · rintro ⟨T,hT⟩; exact ⟨T,T.property,hT⟩
  · rintro ⟨T,hT,hx⟩; exact ⟨⟨T,hT⟩,hx⟩
lemma assemblyRetainedIndex_card (μ : Measure V) (N B : ℕ) (sig : ℝ) :
    Fintype.card (assemblyRetainedIndex μ N B sig)=
      (retainedClassLabels μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-sig)))).card := by
  classical
  exact Fintype.card_coe _
end GraphLiteralSupport.CurrentFalconer.TreeND
end

section
namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory Filter
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))
noncomputable def direction {n : ℕ} (x y : Space n) : Space n := (dist x y)⁻¹ • (x-y)
noncomputable def productFilter {n : ℕ} (I : Finset ℕ) (X Y : ℕ → Set (Space n)) : Set (Space n × Space n) :=
  ⋃ l∈I, X l ×ˢ Y l
def originalDistances {n : ℕ} (E : Set (Space n)) : Set ℝ :=
  {r | ∃ x∈E, ∃ y∈E, dist x y=r}

def StartingPairFilters (n : ℕ) (μ ν : Measure (Space n)) (E₁ E₂ : Set (Space n)) : Prop :=
  ∃ omega₀ : ℝ, 0<omega₀ ∧ ∀ omega : ℝ, 0<omega → omega<omega₀ →
    ∃ (I : ℕ → Finset ℕ) (X Y : ℕ → ℕ → Set (Space n)) (A : ℝ) (K : ℕ), 0<A ∧
    (∀ N l, l∈I N → MeasurableSet (X N l) ∧ MeasurableSet (Y N l)) ∧
    (∀ N l, l∈I N → X N l⊆E₁ ∧ Y N l⊆E₂) ∧
    (∀ N, Set.Pairwise (↑(I N) : Set ℕ) (fun l m => Disjoint (X N l ×ˢ Y N l) (X N m ×ˢ Y N m))) ∧
    (∀ N≥K, ((I N).card:ℝ) ≤ A*((2:ℝ)^N)^(2*(n+1:ℝ)*omega)) ∧
    Antitone (fun N => productFilter (I N) (X N) (Y N)) ∧
    0<(μ.prod ν) (⋂ N, productFilter (I N) (X N) (Y N)) ∧
    (∀ e : ℝ, 0<e → ∃ c C : ℝ, 0<c ∧ 0≤C ∧ ∃ L : ℕ, ∀ N≥L,
      ∃ good : Set (Space n × Space n), MeasurableSet good ∧
      good⊆productFilter (I N) (X N) (Y N) ∧
      (μ.prod ν) (productFilter (I N) (X N) (Y N)\good) ≤ ENNReal.ofReal (C*((2:ℝ)^N)^(-c)) ∧
      (∀ᵐ x ∂μ, ∀ w : Space n, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹≤r → r≤1 →
        ν {y | (x,y)∈good ∧ direction x y∈ball w r} ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^((n+1:ℝ)/2))) ∧
      (∀ᵐ y ∂ν, ∀ w : Space n, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹≤r → r≤1 →
        μ {x | (x,y)∈good ∧ direction x y∈ball w r} ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^((n+1:ℝ)/2))))

end CurrentFalconer.AssemblyCompletion
namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory
open GraphLiteralSupport.CurrentFalconer.TreeND
variable {n : ℕ}
lemma root_of_coordinates {x : Space n} (h : ∀ i, 0≤x i ∧ x i<1) : x∈treeCell [] := by
  simpa [treeCell,GraphLiteralSupport.CurrentFalconer.ambientGridCell,pathIndex] using h
lemma productFilter_measurable (I : Finset ℕ) (X Y : ℕ → Set (Space n))
    (h : ∀ l∈I, MeasurableSet (X l) ∧ MeasurableSet (Y l)) :
    MeasurableSet (productFilter I X Y) := by
  exact MeasurableSet.biUnion (s:=I) (to_countable _) (fun l hl => (h l hl).1.prod (h l hl).2)
lemma productFilter_subset (I : Finset ℕ) (X Y : ℕ → Set (Space n)) (E₁ E₂ : Set (Space n))
    (h : ∀ l∈I, X l⊆E₁ ∧ Y l⊆E₂) : productFilter I X Y⊆E₁×ˢ E₂ := by
  intro z hz
  obtain ⟨l,hl,hz⟩ := mem_iUnion₂.mp hz
  exact ⟨(h l hl).1 hz.1,(h l hl).2 hz.2⟩
end CurrentFalconer.AssemblyCompletion
end

section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter
open scoped ENNReal
lemma complex_positive_sub_variation (α τ : FiniteMeasure ℝ)
    (h : (τ : Measure ℝ)≤(α : Measure ℝ)) :
    (complexOfPositive α-complexOfPositive τ).variation=(α : Measure ℝ)-(τ : Measure ℝ) := by
  let β : FiniteMeasure ℝ := ⟨(α:Measure ℝ)-(τ:Measure ℝ),inferInstance⟩
  have he : complexOfPositive α-complexOfPositive τ=complexOfPositive β := by
    apply sub_eq_iff_eq_add.mpr
    have hh : (α:Measure ℝ)=(β:Measure ℝ)+(τ:Measure ℝ) := (Measure.sub_add_cancel_of_le h).symm
    unfold complexOfPositive
    rw [Measure.toSignedMeasure_congr hh,Measure.toSignedMeasure_add]
    ext s
    simp only [SignedMeasure.toComplexMeasure_apply,add_apply]
    apply Complex.ext <;> simp
  rw [he,complexOfPositive_variation]
  rfl
lemma complexVariationError_positive (α τ : FiniteMeasure ℝ)
    (h : (τ:Measure ℝ)≤(α:Measure ℝ)) :
    complexVariationError α (complexOfPositive τ)=((α:Measure ℝ)-(τ:Measure ℝ)).real univ := by
  rw [complexVariationError,complex_positive_sub_variation α τ h]
lemma complexShellEnergy_positive (τ : FiniteMeasure ℝ) (N : ℕ) :
    complexShellEnergy (complexOfPositive τ) N =
      ∫ r in {r : ℝ | ((2:ℝ)^N)/2≤|r| ∧ |r|≤2*((2:ℝ)^N)}, ‖charFun (τ:Measure ℝ) r‖^2 := by
  have hs : PlanarFalconer.dyadicShell N={r : ℝ | ((2:ℝ)^N)/2≤|r| ∧ |r|≤2*((2:ℝ)^N)} := by
    ext r
    simp only [PlanarFalconer.dyadicShell,mem_ofPred_eq,Real.rpow_sub (by norm_num : (0:ℝ)<2),
      Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one,Real.rpow_natCast,mul_comm]
  rw [complexShellEnergy,hs]
  apply setIntegral_congr_fun (by measurability)
  intro r _
  have he := complexChar_positive τ (-r)
  rw [complexChar_eq_fourier,neg_neg] at he
  dsimp only
  rw [he]
  simp only [charFun_neg,Complex.norm_conj]
end CurrentFalconer.MonotoneShell
end

section
namespace CurrentFalconer.AssemblyCompletion
open MeasureTheory Set Filter
open scoped ENNReal Topology
lemma completion_of_eventual_positive_approximants
    (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (hmono : Antitone (fun N => (α N : Measure ℝ)))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop (𝓝 ((αinf:Measure ℝ) s)))
    (η γ A B : ℝ) (hη : 0<η) (hγ : 0<γ) (hA : 0≤A) (hB : 0≤B)
    (happrox : ∀ᶠ N : ℕ in atTop, ∃ τ : FiniteMeasure ℝ,
      (τ:Measure ℝ)≤(α N:Measure ℝ) ∧
      ((α N:Measure ℝ)-(τ:Measure ℝ)) univ≤ENNReal.ofReal (A*(2:ℝ)^(-η*(N:ℝ))) ∧
      (∫ r in {r : ℝ | ((2:ℝ)^N)/2≤|r| ∧ |r|≤2*((2:ℝ)^N)}, ‖charFun (τ:Measure ℝ) r‖^2)≤
        B*(2:ℝ)^(-γ*(N:ℝ))) :
    (αinf:Measure ℝ)≪volume := by
  classical
  obtain ⟨K,hK⟩ := eventually_atTop.mp happrox
  have hh : ∀ N, ∃ τ : FiniteMeasure ℝ, K≤N →
      (τ:Measure ℝ)≤(α N:Measure ℝ) ∧
      ((α N:Measure ℝ)-(τ:Measure ℝ)) univ≤ENNReal.ofReal (A*(2:ℝ)^(-η*(N:ℝ))) ∧
      (∫ r in {r : ℝ | ((2:ℝ)^N)/2≤|r| ∧ |r|≤2*((2:ℝ)^N)}, ‖charFun (τ:Measure ℝ) r‖^2)≤
        B*(2:ℝ)^(-γ*(N:ℝ)) := by
    intro N
    by_cases hN : K≤N
    · obtain ⟨τ,hτ⟩ := hK N hN
      exact ⟨τ,fun _ => hτ⟩
    · exact ⟨0,fun h => False.elim (hN h)⟩
  choose τ hτ using hh
  apply MonotoneShell.monotone_measure_shell_criterion_of_decay 0 α αinf
    (fun N => MonotoneShell.complexOfPositive (τ N)) (fun _ => inferInstance)
    (fun N _ => hmono (Nat.le_succ N)) hlim hη hγ hB K
  · intro N hN
    rw [MonotoneShell.complexVariationError_positive _ _ (hτ N hN).1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hτ N hN).2.1
  · intro N hN
    rw [MonotoneShell.complexShellEnergy_positive]
    exact (hτ N hN).2.2
end CurrentFalconer.AssemblyCompletion
end

section
namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory
open GraphLiteralSupport.CurrentFalconer.TreeND
open scoped ENNReal
lemma restoration_scalar_bound {n p N : ℕ} (sig c C δ : ℝ) (hC : 0≤C) (hδ : 0<δ)
    (a b z : ℝ≥0∞) (i j : ℕ)
    (hi : (i:ℝ)≤completionPoly n p N) (hj : (j:ℝ)≤completionPoly n p N)
    (ha : a≤ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
      ENNReal.ofReal (completionPoly n p N)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)))
    (hb : b≤ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
      ENNReal.ofReal (completionPoly n p N)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)))
    (hz : z≤ENNReal.ofReal (C*((2:ℝ)^N)^(-c))) :
    ENNReal.ofReal (δ^(-(n:ℝ)/2))*(a+b+z+
      ENNReal.ofReal (((i+j:ℕ):ℝ)*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)))≤
        ENNReal.ofReal (completionError n p N sig c C δ) := by
  have hp : 0≤completionPoly n p N := by unfold completionPoly; positivity
  let D := ((2:ℝ)^N)^(-2:ℝ)+completionPoly n p N*((2:ℝ)^N)^(-sig)
  have hD : 0≤D := by dsimp [D]; positivity
  have hd : ENNReal.ofReal D=ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
      ENNReal.ofReal (completionPoly n p N)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_mul hp]
  have hh : ENNReal.ofReal (((i+j:ℕ):ℝ)*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig))≤
      ENNReal.ofReal (2*completionPoly n p N*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
    push_cast
    linarith
  have hsum := add_le_add (add_le_add (add_le_add (ha.trans_eq hd.symm) (hb.trans_eq hd.symm)) hz) hh
  apply (mul_le_mul_right hsum (ENNReal.ofReal (δ^(-(n:ℝ)/2)))).trans_eq
  have he : completionError n p N sig c C δ=δ^(-(n:ℝ)/2)*(D+D+C*((2:ℝ)^N)^(-c)+
      2*completionPoly n p N*((N+1:ℝ)^3+1)*((2:ℝ)^N)^(-sig)) := by
    unfold completionError D; ring
  conv_rhs =>
    rw [he,ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add hD hD]
end CurrentFalconer.AssemblyCompletion
end
end

end OAI
