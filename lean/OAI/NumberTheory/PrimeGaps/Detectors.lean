import OAI.NumberTheory.PrimeGaps.EqualityPatterns

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

theorem pattern_singular_sum {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    (∑ b∈patternClass (α:=Fin h) r,
      singularSeries (Finset.univ.image fun i => a+(b i:ℕ))) =
    ∑ n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a),
      singularSeries (Finset.univ.image (boxTuple (fun _ => a) n)) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h a)
  intro b
  rw [patternTupleEquiv_image r h a b]

theorem ker_comp_injective {ι α β : Type*} (b : ι → α) (f : α → β) (hf : Function.Injective f) :
    Setoid.ker (f∘b)=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  exact hf.eq_iff

theorem numericPattern_int_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (fun i => (numericPattern r i:ℤ))=r := by
  have h := ker_comp_injective (numericPattern r) (fun n : ℕ => (n:ℤ)) (by intro m n hm; exact_mod_cast (show (m:ℤ)=(n:ℤ) from hm))
  exact h.trans (numericPattern_ker r)

theorem shiftFamily_eq_of_ker {ι : Type*} [Fintype ι] (b c : ι → ℤ)
    (h : Setoid.ker b=Setoid.ker c) : shiftFamily b=shiftFamily c := by
  classical
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  have hc (i j : ι) : b i=b j ↔ c i=c j := by
    change (Setoid.ker b) i j ↔ (Setoid.ker c) i j
    rw [h]
  constructor <;> rintro ⟨hS,he⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mp (he i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mpr (he i hi j hj)⟩

noncomputable def equalityPatternFamily {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Finset (Finset ι) := shiftFamily (fun i => (numericPattern r i:ℤ))

theorem equalityPatternFamily_sign_sum {ι : Type*} [Fintype ι] (r : Setoid ι) :
    (∑ S∈equalityPatternFamily r,(-1:ℤ)^S.card)=-(Fintype.card (Quotient r):ℤ) := by
  classical
  rw [equalityPatternFamily,shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => (numericPattern r i:ℤ))=
      Finset.univ.image (fun j : Fin (Fintype.card (Quotient r)) => (j.val:ℤ)) := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fintype.equivFin (Quotient r) (Quotient.mk r i),rfl⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
      refine ⟨i,?_⟩
      simp only [numericPattern,hi,Equiv.apply_symm_apply]
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem translated_shiftFamily {ι : Type*} [Fintype ι] {h : ℕ}
    (r : Setoid ι) (a : ℕ) (b : ι → Fin h) (hb : b∈patternClass r) :
    shiftFamily (fun i => ((a+(b i).val:ℕ):ℤ))=equalityPatternFamily r := by
  apply shiftFamily_eq_of_ker
  rw [numericPattern_int_ker]
  have hi : Function.Injective (fun x : Fin h => ((a+x.val:ℕ):ℤ)) := by
    intro i j hij
    apply Fin.ext
    have hh : a+i.val=a+j.val := by exact_mod_cast (show ((a+i.val:ℕ):ℤ)=((a+j.val:ℕ):ℤ) from hij)
    exact Nat.add_left_cancel hh
  exact (ker_comp_injective b _ hi).trans ((mem_patternClass r b).mp hb)

theorem divisorSum_fin_zero (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    divisorSum X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [divisorSum,h,Finset.sum_singleton]
  simp only [divisorCoefficient,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i

theorem divisorSum_singleton_at_prime {X M b : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hp : Nat.Prime (M+b)) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) :
    divisorSum X G M (fun _ => b)=G 0 := by
  have ht : (fun _ : Fin 1 => b)=Fin.snoc (0 : Fin 0 → ℕ) b := by ext i; fin_cases i; rfl
  rw [ht,divisorSum_prime_delete hX hM hp G hrho hbudget,divisorSum_fin_zero]
  congr 1

theorem theta_div_log_le_upper {X M b Y : ℕ} (hX : 2≤X) (hY : M+b≤Y) (hYP : 1≤Y) :
    theta (M+b)/Real.log X≤Real.log Y/Real.log X := by
  apply div_le_div_of_nonneg_right _ (log_pos_of_two_le hX).le
  by_cases hp : Nat.Prime (M+b)
  · rw [theta,ite_eq_left hp]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hY)
  · rw [theta,ite_eq_right hp]
    exact Real.log_nonneg (by exact_mod_cast hYP)

theorem singleton_divisor_majorant {X M b Y : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hY : M+b≤Y) (hYP : 1≤Y) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    theta (M+b)/Real.log X≤(Real.log Y/Real.log X)*divisorSum X G M (fun _ => b)^2 := by
  by_cases hp : Nat.Prime (M+b)
  · rw [divisorSum_singleton_at_prime hX hM hp G hrho hbudget,hG,one_pow,mul_one]
    exact theta_div_log_le_upper hX hY hYP
  · rw [theta,ite_eq_right hp,zero_div]
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hYP))
      (log_pos_of_two_le hX).le) (sq_nonneg _)

theorem sum_square_diagonal_offdiag {α : Type*} [DecidableEq α]
    (B : Finset α) (f : α → ℝ) :
    (∑ b∈B,f b)^2=(∑ b∈B,f b^2)+∑ b∈B,∑ c∈B.erase b,f b*f c := by
  rw [pow_two,Finset.sum_mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←Finset.sum_erase_add B (fun c => f b*f c) hb]
  ring

theorem detector_square_majorant {X M Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ b∈B, X<M+b) (hY : ∀ b∈B, M+b≤Y)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    detector X B M^2≤(Real.log Y/Real.log X)*detector X B M+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G M (fun _ => b)^2*divisorSum X G M (fun _ => c)^2 := by
  classical
  let t := fun b => theta (M+b)/Real.log X
  let q := Real.log Y/Real.log X
  let D := fun b => divisorSum X G M (fun _ => b)
  have ht (b : ℕ) : 0≤t b := div_nonneg (theta_nonneg _) (log_pos_of_two_le hX).le
  have hq : 0≤q := div_nonneg (Real.log_nonneg (by exact_mod_cast hYP)) (log_pos_of_two_le hX).le
  have he : detector X B M=∑ b∈B,t b := by rw [detector,Finset.sum_div]
  have hupper (b : ℕ) (hb : b∈B) : t b≤q := theta_div_log_le_upper hX (hY b hb) hYP
  have hmajor (b : ℕ) (hb : b∈B) : t b≤q*(D b)^2 :=
    singleton_divisor_majorant hX (hM b hb) (hY b hb) hYP G hrho hbudget hG
  rw [he,sum_square_diagonal_offdiag,Finset.mul_sum,Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b hb
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hupper b hb) (ht b)
  · apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have hcB := Finset.mem_of_mem_erase hc
    have hh := mul_le_mul (hmajor b hb) (hmajor c hcB) (ht c)
      (mul_nonneg hq (sq_nonneg (D b)))
    dsimp [q,D] at hh
    nlinarith

noncomputable def patternBoxShifts {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h) : Fin n → ℕ :=
  fun i => a (p i)+(u (p i):ℕ)

theorem patternBoxShifts_family {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    shiftFamily (fun i => (patternBoxShifts p a u i:ℤ))=
      shiftFamily (fun i => ((p i).val:ℤ)) := by
  apply shiftFamily_eq_of_ker
  apply Setoid.ext
  intro i j
  have hi := (Finset.mem_filter.mp hu).2
  change ((patternBoxShifts p a u i:ℤ)=(patternBoxShifts p a u j:ℤ)) ↔
    ((p i).val:ℤ)=((p j).val:ℤ)
  have he (i : Fin n) : (patternBoxShifts p a u i:ℤ)=boxTuple (fun j => (a j:ℤ)) u (p i) := by
    simp only [patternBoxShifts,boxTuple,Nat.cast_add]
  rw [he,he,hi.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; apply Fin.ext; exact_mod_cast h

theorem patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin s → ℕ) (u : Fin s → Fin h) :
    (Finset.univ.image fun i => (patternBoxShifts p a u i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩ := hp j
    exact ⟨i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩

theorem surjective_shiftFamily_sign_sum {n s : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) :
    (∑ S∈shiftFamily (fun i => ((p i).val:ℤ)),(-1:ℤ)^S.card)=-(s:ℤ) := by
  classical
  rw [shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => ((p i).val:ℤ))=
      Finset.univ.image (fun j : Fin s => (j.val:ℤ)) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨p i,rfl⟩
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩ := hp j; exact ⟨i,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij; apply Fin.ext; exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem box_sum_scaled_norm_le {s h : ℕ} (a : Fin s → ℤ)
    (f g : (Fin s → Fin h) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (herr : ∀ u∈distinctBox a, ‖(L:ℂ)^s*f u-g u‖≤E) :
    ‖(∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s‖≤((h:ℝ)/L)^s*E := by
  classical
  have hb : ‖∑ u∈distinctBox a,((L:ℂ)^s*f u-g u)‖≤(h:ℝ)^s*E := by
    calc
      _ ≤ ∑ _u∈distinctBox (h:=h) a,E := norm_sum_le_of_le _ herr
      _ = ((distinctBox (h:=h) a).card:ℝ)*E := by simp
      _ ≤ (h:ℝ)^s*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        have hc := Finset.card_le_card (show distinctBox (h:=h) a⊆Finset.univ from Finset.subset_univ _)
        simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
          (show ((distinctBox (h:=h) a).card:ℝ)≤(Fintype.card (Fin s → Fin h):ℝ) from by exact_mod_cast hc)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hb
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s=
      ((L:ℂ)^s*(∑ u∈distinctBox a,f u)-∑ u∈distinctBox a,g u)/(L:ℂ)^s := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans hb
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem box_sum_errors_tendsto_zero (s : ℕ) (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ)
    (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (Fin s → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop,0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ u∈distinctBox (a X),‖(L X:ℂ)^s*f X u-g X u‖≤E X) :
    Tendsto (fun X => (∑ u∈distinctBox (a X),f X u)-
      (∑ u∈distinctBox (a X),g X u)/(L X:ℂ)^s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun X => ((H X:ℝ)/L X)^s*|E X|)
  · filter_upwards [hL,herr] with X hLX hX
    exact box_sum_scaled_norm_le (a X) (f X) (g X) hLX (abs_nonneg _) (fun u hu =>
      (hX u hu).trans (le_abs_self _))
  · simpa only [abs_zero,mul_zero] using (hHL.pow s).mul hE.abs

theorem natural_boxDiameterBound {s h K : ℕ} (a : Fin s → ℕ) (ha : ∀ j,a j≤K*h) :
    boxDiameterBound (h:=h) (fun j => (a j:ℤ)) ((K+1)*h) := by
  intro u i j
  dsimp [boxTuple]
  have hi := (u i).isLt
  have hj := (u j).isLt
  have hai := ha i
  have haj := ha j
  have hk : K*h+h=(K+1)*h := by ring
  omega

theorem unmarked_box_pattern_limit {n s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (p : Fin (n+1) → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^s*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin s → Fin (H X)) =>
    (average X (fun m => divisorSum X F m (patternBoxShifts p (a X) u)):ℂ)
  let g := fun X (u : Fin s → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  obtain ⟨E,hE,herr⟩ := unmarked_average_uniform_asymptotic F rho hrho hrho1 hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp)
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^s*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hcut
    intro u hu
    have hb (i : Fin (n+1)) : patternBoxShifts p (a X) u i≤(K+1)*H X := by
      have hi := (u (p i)).isLt
      have hh := haX (p i)
      dsimp [H] at hi
      dsimp [patternBoxShifts,H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (a X) u) (patternBoxShifts_family p (a X) u hu)
       ((K+1)*H X) hb (by simpa only [Nat.mul_assoc] using hcut)
    rw [patternBoxShifts_image p hp] at hz
    exact hz
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have he := box_sum_errors_tendsto_zero s H az (fun X => Real.log X) E lam f g hL hHL hE herror
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s)
      atTop (𝓝 ((lam:ℂ)^s*c)) := by
    have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
    have hh' := hh.mul_const c
    simp only [Complex.ofReal_one,mul_one] at hh'
    apply hh'.congr'
    filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
    have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c =
      (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^s
    simp only [g,←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [div_pow]
    field_simp
  have h := he.add hmain
  simp only [sub_add_cancel,zero_add] at h
  exact h

theorem average_mono {X : ℕ} (f g : ℕ → ℝ)
    (h : ∀ m∈Finset.Ioc X (2*X),f m≤g m) : average X f≤average X g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg X)

theorem average_add (X : ℕ) (f g : ℕ → ℝ) :
    average X (fun m => f m+g m)=average X f+average X g := by
  rw [average,Finset.sum_add_distrib,add_div]
  rfl

theorem average_const_mul (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    average X (fun m => c*f m)=c*average X f := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]

theorem average_finset_sum {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    average X (fun m => ∑ i∈S,f i m)=∑ i∈S,average X (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

theorem weighted_detector_square_majorant {X Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, X < m+b)
    (hY : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, m+b ≤ Y)
    (W : ℕ → ℝ) (hW : ∀ m∈Finset.Ioc X (2*X),0≤W m)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    average X (fun m => W m*detector X B m^2)≤
      (Real.log Y/Real.log X)*average X (fun m => W m*detector X B m)+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        average X (fun m => W m*divisorSum X G m (fun _ => b)^2*
          divisorSum X G m (fun _ => c)^2) := by
  classical
  have hh := average_mono (X:=X) (fun m => W m*detector X B m^2)
    (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) (by
      intro m hm
      exact mul_le_mul_of_nonneg_left (detector_square_majorant hX hYP B
        (hM m hm) (hY m hm) G hrho hbudget hG) (hW m hm))
  have he : (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2))=
      (fun m => (Real.log Y/Real.log X)*(W m*detector X B m)+
        (Real.log Y/Real.log X)^2*(∑ b∈B,∑ c∈B.erase b,
          W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) := by
    funext m
    have hs : (∑ b∈B,∑ c∈B.erase b,
        W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)=
        W m*(∑ b∈B,∑ c∈B.erase b,
          divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2) := by
      simp only [Finset.mul_sum,mul_assoc]
    rw [hs]
    ring
  rw [he,average_add,average_const_mul,average_const_mul,
    average_finset_sum] at hh
  simpa only [average_finset_sum] using hh

theorem detector_log_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ => (Real.log (X:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hH : Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 0) := by
    have hlogratio : Tendsto (fun X : ℕ => Real.log (X:ℝ)/(X:ℝ)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    apply squeeze_zero' (Eventually.of_forall (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact div_le_div_of_nonneg_right (blockLength_le_mul_log hlam hX) (Nat.cast_nonneg X)
    · simpa only [mul_div_assoc,mul_zero] using hlogratio.const_mul lam
  have harg : Tendsto (fun X : ℕ => 2+2*(blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 2) := by
    simpa only [mul_zero,add_zero,mul_div_assoc] using tendsto_const_nhds.add (hH.const_mul 2)
  have hh := ((Real.continuousAt_log (by norm_num : (2:ℝ)≠0)).tendsto.comp harg).mul hinv
  have hh' := (tendsto_const_nhds (x := (1:ℝ))).add hh
  simp only [mul_zero,add_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXP : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL := log_pos_of_two_le hX
  have hA : 0<2+2*(blockLength lam X:ℝ)/(X:ℝ) := by positivity
  have he : (2*(X:ℝ)+2*blockLength lam X)=(X:ℝ)*(2+2*(blockLength lam X:ℝ)/(X:ℝ)) := by
    field_simp
  simp only [Function.comp_apply]
  rw [he,Real.log_mul hXP.ne' hA.ne',add_div,div_self hL.ne']
  rfl

theorem exists_normalized_singleton_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧ (∀ v,0≤f v) ∧ (∫ v,f v)=1 := by
  have hopen : IsOpen (positiveSimplex 1 tau) := by
    have he : positiveSimplex 1 tau=(fun v : Fin 1 → ℝ => v 0) ⁻¹' Ioo 0 tau := by
      ext v
      simp [positiveSimplex,coordinateSum,Fin.forall_fin_one]
    rw [he]
    exact isOpen_Ioo.preimage (continuous_apply 0)
  have hmem : (fun _ : Fin 1 => tau/2)∈positiveSimplex 1 tau := by
    simp only [positiveSimplex,Set.mem_ofPred_eq,coordinateSum,Fin.sum_univ_one]
    constructor
    · intro i; positivity
    · linarith
  obtain ⟨f,hs,hc,hf,h01,h1⟩ := exists_contDiff_tsupport_subset (n:=(⊤:ℕ∞)) (hopen.mem_nhds hmem)
  have hn : ∀ v,0≤f v := fun v => (h01 (Set.mem_range_self v)).1
  let A := ∫ v,f v
  have hA : 0<A := integral_pos_of_integrable_nonneg_nonzero hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hc) hn (by rw [h1]; norm_num)
  let g := fun v => f v/A
  have hgc : HasCompactSupport g := hc.comp_left (g:=fun x : ℝ => x/A) (by simp)
  have hgs : tsupport g⊆positiveSimplex 1 tau :=
    (tsupport_comp_subset (g:=fun x : ℝ => x/A) (by simp) f).trans hs
  refine ⟨g,hf.div_const A,hgc,hgs,fun v => div_nonneg (hn v) hA.le,?_⟩
  rw [show g=(fun v => f v/A) from rfl,integral_div]
  exact div_self hA.ne'

theorem exists_detector_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧
      HasBudget (cumulativeProfile tau f) tau ∧
      ContDiff ℝ ∞ (cumulativeProfile tau f) ∧
      HasCompactSupport (cumulativeProfile tau f) ∧
      cumulativeProfile tau f 0=1 := by
  obtain ⟨f,hf,hc,hs,_hn,h1⟩ := exists_normalized_singleton_profile htau
  refine ⟨f,hf,hc,hs,cumulativeProfile_budget tau f hs,
    cumulativeProfile_smooth tau f hc hf,cumulativeProfile_compact tau f hc,?_⟩
  rw [cumulativeProfile_tail tau f hs 0 (fun _ => le_rfl)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,h1]
  intro v hv
  by_contra hne
  apply hv
  intro i
  exact (hs (subset_tsupport f hne)).1 i |>.le

end LargePrimeGaps

end OAI
