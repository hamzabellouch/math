import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι κ N : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype N] [DecidableEq N]

lemma assignments_toFinset (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) : (assignments n₀ l).toFinset=Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro p
  apply List.mem_toFinset.mpr (mem_assignments n₀ l hl p ?_)
  intro i hi
  exfalso
  exact hi (List.mem_toFinset.mp (by rw [hall]; exact Finset.mem_univ i))

lemma assignments_nodup (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) : (assignments n₀ l).Nodup := by
  classical
  change (↑(assignments n₀ l) : Multiset (ι → N)).Nodup
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (assignments n₀ l).toFinset.card=(assignments n₀ l).length
  rw [assignments_toFinset n₀ l hl hall,Finset.card_univ,Fintype.card_fun,length_assignments]
  congr 1
  simpa only [hall,Finset.card_univ] using (List.toFinset_card_of_nodup hl)

lemma assignments_sum (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) (f : (ι → N) → ℝ) :
    ((assignments n₀ l).map f).sum=∑ p, f p := by
  classical
  rw [← List.sum_toFinset _ (assignments_nodup n₀ l hl hall),
    assignments_toFinset n₀ l hl hall]

theorem jet_prod_sum {f : N → E → ℝ} (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (n₀ : N) (v : ι → E) (l : List ι) (hl : l.Nodup) (hall : l.toFinset=Finset.univ) :
    jet v l (fun x => ∏ n, f n x) = fun x =>
      ∑ p : ι → N, ∏ n, jet v (l.filter (fun i => p i=n)) (f n) x := by
  rw [jet_prod hf n₀ v l hl]
  funext x
  exact assignments_sum n₀ l hl hall _

omit [Fintype κ] [DecidableEq κ] in
lemma smooth_right_jet {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : κ → F) (k : List κ) (ω : F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => jet w k (fun ω => f (θ,ω)) ω) := by
  simp_rw [jet_right_slice hf]
  exact (smooth_jet hf _ k).comp (contDiff_id.prodMk contDiff_const)

theorem mixedJet_prod_sum {f : N → E × F → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) (n₀ : N)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) :
    mixedJet v w l k (fun x => ∏ n, f n x) =
      ∑ p : ι → N, ∑ q : κ → N,
        ∏ n, mixedJet v w (l.filter (fun i => p i=n)) (k.filter (fun j => q j=n)) (f n) := by
  unfold mixedJet
  have hr (θ : E) : jet w k (fun ω => ∏ n, f n (θ,ω)) = fun ω =>
      ∑ q : κ → N, ∏ n, jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) ω :=
    jet_prod_sum (fun n => (hf n).comp (contDiff_const.prodMk contDiff_id)) n₀ w k hk hkall
  simp_rw [hr]
  rw [jet_sum _ (fun q hq => contDiff_prod (fun n _ => smooth_right_jet (hf n) w _ 0))]
  have hleft (q : κ → N) : jet v l (fun θ => ∏ n,
      jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) 0) = fun θ =>
      ∑ p : ι → N, ∏ n, jet v (l.filter (fun i => p i=n))
        (fun θ => jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) 0) θ :=
    jet_prod_sum (fun n => smooth_right_jet (hf n) w _ 0) n₀ v l hl hlall
  simp_rw [hleft]
  exact Finset.sum_comm

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ N : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ] [Fintype N] [DecidableEq N]

omit [BorelSpace E] [SecondCountableTopology E] [DecidableEq κ] [Fintype N] in
lemma slotPolynomial_fiber (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (p : ι → N) (n : N) (x : E) :
    slotPolynomial μ b a (Finset.univ.filter (fun i => p i=n)) x =
      slotPolynomial μ b (fun j : {j : ι // p j=n} => a j) Finset.univ x := by
  have he : (Finset.univ : Finset {j : ι // p j=n}).image Subtype.val =
      Finset.univ.filter (fun j => p j=n) := by ext j; simp
  have hm : moments μ (fun j : {j : ι // p j=n} => coordinate b (a j)) =
      fun t => moments μ (fun j : ι => coordinate b (a j)) (t.image Subtype.val) := by
    funext t
    exact moments_image μ (fun j : ι => coordinate b (a j)) Subtype.val Subtype.val_injective t
  unfold slotPolynomial
  rw [hm]
  simpa only [Function.comp_def,he] using
    (polynomial_image (fun j : {j : ι // p j=n} => j.val) Subtype.val_injective
      (moments μ (fun j : ι => coordinate b (a j))) Finset.univ
      (fun j => coordinate b (a j) x)).symm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Fintype N] in
lemma filter_nil_iff_card_fiber (l : List ι) (hall : l.toFinset=Finset.univ)
    (p : ι → N) (n : N) :
    l.filter (fun i => p i=n)=[] ↔ Fintype.card {i : ι // p i=n}=0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_⟩
    have hi : i.val ∈ l := List.mem_toFinset.mp (by rw [hall]; exact Finset.mem_univ _)
    have hh : i.val ∈ l.filter (fun j => p j=n) := List.mem_filter.mpr ⟨hi,by simpa using i.prop⟩
    simp [h] at hh
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have hh := (List.mem_filter.mp hi).2
    exact h.false ⟨i,by simpa using hh⟩

omit [DecidableEq κ] [Fintype N] in
lemma mixedJet_reduced_fibers {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (p : ι → N) (q : ϑ → N) (n : N) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j))
      (l.filter (fun i => p i=n)) (k.filter (fun j => q j=n)) (fun x => crossMGF μ x-1) =
      reducedCrossMoment μ b (fun i : {i : ι // p i=n} => a i)
        (fun j : {j : ϑ // q j=n} => c j) := by
  unfold reducedCrossMoment
  split_ifs with hempty
  · apply mixedJet_reduced_unmixed hμ
    simpa only [filter_nil_iff_card_fiber l hlall p n,
      filter_nil_iff_card_fiber k hkall q n] using hempty
  · rw [mixedJet_reduced hμ _ _ _ _ (hl.filter _) (hk.filter _)]
    · change (∫ x, slotPolynomial μ b a (l.filter (fun i => p i=n)).toFinset x *
        slotPolynomial μ b c (k.filter (fun j => q j=n)).toFinset x ∂μ)=_
      simp only [List.toFinset_filter,decide_eq_true_eq,hlall,hkall]
      simp only [slotPolynomial_fiber,crossMoment]
    · intro h
      apply hempty
      exact Or.inl ((filter_nil_iff_card_fiber l hlall p n).mp h.1)

omit [DecidableEq κ] in

lemma mixedJet_reduced_pow {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) (m : ℕ) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => (crossMGF μ x-1)^(m+1)) =
      ∑ p : ι → Fin (m+1), ∑ q : ϑ → Fin (m+1), crossBlockProduct μ b p q a c := by
  have hp : (fun x => (crossMGF μ x-1)^(m+1)) =
      (fun x => ∏ _i : Fin (m+1), (crossMGF μ x-1)) := by funext x; simp
  rw [hp,JetCalculus.mixedJet_prod_sum (fun _ => (smooth_crossMGF hμ).sub contDiff_const)
    (0 : Fin (m+1)) _ _ l k hl hlall hk hkall]
  simp only [crossBlockProduct,mixedJet_reduced_fibers hμ b a c l k hl hlall hk hkall]

omit [BorelSpace E] [SecondCountableTopology E] [DecidableEq κ] in
lemma mixedCumulant_eq_range (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) :
    mixedCumulant μ b a c =
      ∑ m ∈ Finset.range (Fintype.card ι+Fintype.card ϑ),
        ((-1:ℝ)^m/(m+1)) *
          (∑ p : ι → Fin (m+1), ∑ q : ϑ → Fin (m+1), crossBlockProduct μ b p q a c) := by
  unfold mixedCumulant
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type,← Finset.mul_sum]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,logCoefficient,Nat.cast_zero,div_zero,zero_mul,zero_add,Fin.val_succ]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  ring

omit [DecidableEq κ] in

lemma mixedJet_log_crossMGF {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => Real.log (crossMGF μ x)) = mixedCumulant μ b a c := by
  have hlc : l.length=Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hl,hlall,Finset.card_univ]
  have hkc : k.length=Fintype.card ϑ := by
    rw [← List.toFinset_card_of_nodup hk,hkall,Finset.card_univ]
  rw [JetCalculus.mixedJet_logTrunc (smooth_crossMGF hμ) (crossMGF_pos hμ)
    crossMGF_zero _ _ _ _ hl hk,hlc,hkc,mixedCumulant_eq_range]
  unfold JetCalculus.logTrunc
  rw [JetCalculus.mixedJet_sum _ (fun m _ => contDiff_const.mul
    (((smooth_crossMGF hμ).sub contDiff_const).pow _))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [JetCalculus.mixedJet_const_mul (((smooth_crossMGF hμ).sub contDiff_const).pow _),
    mixedJet_reduced_pow hμ b a c l k hl hlall hk hkall]

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma mixedJet_fst (f : E → ℝ) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hk : k≠[]) : mixedJet v w l k (fun x => f x.1)=0 := by
  simp only [mixedJet,jet_const,hk,↓reduceIte]
  split_ifs <;> rfl

lemma mixedJet_snd (f : F → ℝ) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l≠[]) : mixedJet v w l k (fun x => f x.2)=0 := by
  simp only [mixedJet,jet_const,hl,↓reduceIte]

end JetCalculus
namespace Appell
open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

omit [SecondCountableTopology E] in
lemma log_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (x : E × E) :
    Real.log (crossMGF μ x) =
      Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2)) -
        Real.log (laplace μ (fun _ => (1:ℝ)) x.1) -
        Real.log (laplace μ (fun _ => (1:ℝ)) x.2) := by
  rw [crossMGF,Real.log_mul (inv_ne_zero (laplace_one_pos hμ _).ne')
      (mul_ne_zero (inv_ne_zero (laplace_one_pos hμ _).ne') (laplace_one_pos hμ _).ne'),
    Real.log_mul (inv_ne_zero (laplace_one_pos hμ _).ne') (laplace_one_pos hμ _).ne',
    Real.log_inv,Real.log_inv]
  ring

omit [DecidableEq κ] in

theorem mixedJet_log_laplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))) =
      mixedCumulant μ b a c := by
  have hs := (contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))).log
    (fun θ => (laplace_one_pos hμ θ).ne')
  have hsA : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))) :=
    hs.comp (contDiff_fst.add contDiff_snd)
  have hsL : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) x.1)) := hs.comp contDiff_fst
  have hsR : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) x.2)) := hs.comp contDiff_snd
  have hh := mixedJet_log_crossMGF hμ b a c l k hl hlall hk hkall
  simp_rw [log_crossMGF hμ] at hh
  rw [JetCalculus.mixedJet_sub (hsA.sub hsL) hsR,
    JetCalculus.mixedJet_sub hsA hsL,
    JetCalculus.mixedJet_fst (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) _ _ _ _ hkne,
    JetCalculus.mixedJet_snd (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) _ _ _ _ hlne,
    sub_zero,sub_zero] at hh
  exact hh

theorem actual_cumulant_energy {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β)
    (b : OrthonormalBasis κ ℝ E) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) :
    TensorEnergy.Bound (fun (a : ι → κ) (c : ϑ → κ) =>
      JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
        (fun x => Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))))
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  simp_rw [mixedJet_log_laplace hμ b _ _ l k hl hlall hk hkall hlne hkne]
  exact mixedCumulant_energy μ hμ.hasMoments hβ hP b

end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
