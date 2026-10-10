import OAI.Combinatorics.SquareDifference.FiniteKernel

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
open Finset

lemma rationalGridPoint_injective (q : ℕ) [NeZero q] : Function.Injective (rationalGridPoint q) := by
  intro a b h
  apply ZMod.val_injective
  have hq : (q : ℚ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he := (div_left_inj' hq).mp h
  exact_mod_cast he

lemma exists_rationalGridPoint (q : ℕ) [NeZero q] (b : ℚ)
    (hb0 : 0≤b) (hb1 : b<1) (hbd : b.den∣q) :
    ∃a : ZMod q, rationalGridPoint q a=b := by
  let n : ℕ := b.num.toNat*(q/b.den)
  have hnum : 0≤b.num := Rat.num_nonneg.mpr hb0
  have hqeq : b.den*(q/b.den)=q := Nat.mul_div_cancel' hbd
  have hden0 : (b.den : ℚ)≠0 := Nat.cast_ne_zero.mpr b.den_nz
  have hq0 : (q : ℚ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he : (n:ℚ)/q=b := by
    dsimp only [n]
    rw [Nat.cast_mul,← Int.cast_natCast,Int.toNat_of_nonneg hnum]
    apply (div_eq_iff hq0).mpr
    conv_rhs => rw [← Rat.num_div_den b]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden0).mpr
    have heq : (b.den:ℚ)*(q/b.den:ℕ)=q := by exact_mod_cast hqeq
    calc
      _ = (b.num:ℚ)*((b.den:ℚ)*(q/b.den:ℕ)) := by ring
      _ = _ := by rw [heq]
  have hn : n<q := by
    have : (n:ℚ)<q := (div_lt_one (Nat.cast_pos.mpr (NeZero.pos q))).mp (he.trans_lt hb1)
    exact_mod_cast this
  refine ⟨(n:ZMod q),?_⟩
  unfold rationalGridPoint
  rw [ZMod.val_natCast_of_lt hn]
  exact he

noncomputable def rationalGrid (q : ℕ) [NeZero q] : Finset ℚ :=
  univ.image (rationalGridPoint q)

lemma mem_rationalGrid (q : ℕ) [NeZero q] (b : ℚ) :
    b∈rationalGrid q ↔ 0≤b ∧ b<1 ∧ b.den∣q := by
  classical
  constructor
  · intro h
    obtain ⟨a,_,rfl⟩ := mem_image.mp h
    exact ⟨rationalGridPoint_nonneg q a,rationalGridPoint_lt_one q a,rationalGridPoint_den_dvd q a⟩
  · rintro ⟨h0,h1,hd⟩
    obtain ⟨a,ha⟩ := exists_rationalGridPoint q b h0 h1 hd
    exact mem_image.mpr ⟨a,mem_univ _,ha⟩

lemma sum_rationalGrid {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q] (f : ℚ → E) :
    (∑b∈rationalGrid q,f b)=∑a : ZMod q,f (rationalGridPoint q a) := by
  classical
  exact sum_image (fun _ _ _ _ h => rationalGridPoint_injective q h)

lemma bounded_sum_eq_grid {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q]
    (L : ℕ) (f : ℚ → E)
    (hf : ∀b, 0≤b → b<1 → f b≠0 → b.den≤L ∧ b.den∣q) :
    (∑b∈boundedRationals L,f b)=∑a : ZMod q,f (rationalGridPoint q a) := by
  classical
  rw [← sum_rationalGrid]
  apply sum_congr_of_eq_on_inter
  · intro b hb hbg
    by_contra h
    have hh := hf b ((mem_boundedRationals L b).mp hb).1 ((mem_boundedRationals L b).mp hb).2.1 h
    exact hbg ((mem_rationalGrid q b).mpr ⟨((mem_boundedRationals L b).mp hb).1,
      ((mem_boundedRationals L b).mp hb).2.1,hh.2⟩)
  · intro b hb hbg
    by_contra h
    have hh := hf b ((mem_rationalGrid q b).mp hb).1 ((mem_rationalGrid q b).mp hb).2.1 h
    exact hbg ((mem_boundedRationals L b).mpr ⟨((mem_rationalGrid q b).mp hb).1,
      ((mem_rationalGrid q b).mp hb).2.1,hh.1⟩)
  · intro b hb hbg; rfl

end SquareDifference

namespace SquareDifference

open Finset

lemma bounded_sum_grid_of {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q]
    (L : ℕ) (f : ℚ → E)
    (hf₁ : ∀b∈boundedRationals L, f b≠0 → b.den∣q)
    (hf₂ : ∀b∈rationalGrid q, f b≠0 → b.den≤L) :
    (∑b∈boundedRationals L,f b)=∑a : ZMod q,f (rationalGridPoint q a) := by
  classical
  rw [← sum_rationalGrid]
  apply sum_congr_of_eq_on_inter
  · intro b hb hbg
    by_contra h
    exact hbg ((mem_rationalGrid q b).mpr ⟨((mem_boundedRationals L b).mp hb).1,
      ((mem_boundedRationals L b).mp hb).2.1,hf₁ b hb h⟩)
  · intro b hb hbg
    by_contra h
    exact hbg ((mem_boundedRationals L b).mpr ⟨((mem_rationalGrid q b).mp hb).1,
      ((mem_rationalGrid q b).mp hb).2.1,hf₂ b hb h⟩)
  · intro b hb hbg; rfl

lemma prime_dvd_smallQuadraticModulus_iff {p r : ℕ} (hp : p.Prime) (hr : r.Prime) :
    r∣smallQuadraticModulus p ↔ r=p := by
  unfold smallQuadraticModulus
  split_ifs with h
  · subst p
    constructor
    · intro hd
      have hd2 := hr.dvd_of_dvd_pow (show r∣2^3 by simpa using hd)
      exact ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hr.ne_one
    · rintro rfl; norm_num
  · exact (Nat.dvd_prime hp).trans (or_iff_right hr.ne_one)

section GridModel

variable {I : Type*} [Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

omit [DecidableEq I] [∀i, Fact (p i).Prime] in
lemma primary_cover_of_prime_support (q : ℕ) (hq : q≠0)
    (hs : ∀r, r.Prime → r∣q → ∃i,p i=r) : q∣∏i,primaryModulus q (p i) := by
  classical
  have h := dvd_primaryModulus_product q hq (univ.image p) (by
    intro r hr
    obtain ⟨i,hi⟩ := hs r (Nat.mem_primeFactors.mp hr).1 (Nat.mem_primeFactors.mp hr).2.1
    exact mem_image.mpr ⟨i,mem_univ _,hi⟩)
  rwa [prod_image (fun _ _ _ _ h => hinj h)] at h

omit hinj in
lemma smallProduct_primary_cover {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) :
    b.den∣∏i,primaryModulus b.den (p i) := by
  apply primary_cover_of_prime_support p hinj b.den b.den_nz
  intro r hr hrd
  obtain ⟨i,_,hi⟩ := (prime_dvd_finset_prod_iff (fun i => smallQuadraticModulus (p i)) univ r hr).mp (hrd.trans hb)
  exact ⟨i,((prime_dvd_smallQuadraticModulus_iff (Fact.out : (p i).Prime) hr).mp hi).symm⟩

variable (R : Finset I) (c : ∀i,ZMod (p i))

omit hinj [∀i, Fact (p i).Prime] in
lemma root_active_div_smallProduct (B : Finset I) :
    rootSquareModulus p R*(∏i∈B\R,p i)∣∏i,smallQuadraticModulus (p i) := by
  have h₁ : (∏i∈B\R,p i)∣∏i∈Rᶜ,smallQuadraticModulus (p i) := by
    apply (prod_dvd_prod_of_dvd _ _ (fun i _ => prime_dvd_smallQuadraticModulus (p i))).trans
    exact prod_dvd_prod_of_subset _ _ _ (by intro i hi; exact mem_compl.mpr (mem_sdiff.mp hi).2)
  have h₂ := Nat.mul_dvd_mul_left (rootSquareModulus p R) h₁
  simpa only [rootSquareModulus,smallQuadraticModulus,prod_mul_prod_compl] using h₂

lemma kernelModelCoefficient_den_smallProduct (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (hne : kernelModelCoefficient p R c H b≠0) :
    b.den∣∏i,smallQuadraticModulus (p i) := by
  rw [←primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo] at hne
  exact (primaryModelCoefficient_denominator p hinj b hb R c H htwo hc hne).trans
    (root_active_div_smallProduct p R (primaryActive p b.den))

omit hinj in
instance smallProductNeZero : NeZero (∏i,smallQuadraticModulus (p i)) :=
  ⟨(prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (p i).Prime))).ne'⟩

lemma actualModelTransform_grid (H : ℝ) (L N : ℕ) (α : ℝ)
    (hmodel : (rootSquareModulus p R:ℝ)*H≤L)
    (hcover : ∀b : ℚ,b.den≤L → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0) :
    actualModelTransform p R c H L N α=
      ∑a : ZMod (∏i,smallQuadraticModulus (p i)),
        kernelModelCoefficient p R c H (rationalGridPoint _ a)*
          normalizedLinearSum N (α-rationalGridPoint _ a) := by
  let : NeZero (∏i,smallQuadraticModulus (p i)) :=
    ⟨(prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (p i).Prime))).ne'⟩
  unfold actualModelTransform
  rw [Finset.sum_coe_sort (boundedRationals L) (fun b : ℚ =>
    kernelModelCoefficient p R c H b*normalizedLinearSum N (α-b))]
  apply bounded_sum_grid_of
  · intro b hb hh
    exact kernelModelCoefficient_den_smallProduct p hinj R c b
      (hcover b ((mem_boundedRationals L b).mp hb).2.2) H htwo hc (left_ne_zero_of_mul hh)
  · intro b hb hh
    have hb' := smallProduct_primary_cover p hinj b ((mem_rationalGrid _ b).mp hb).2.2
    have hne := left_ne_zero_of_mul hh
    rw [← primaryModelCoefficient_eq_kernelModel p R c hinj b hb' H htwo] at hne
    have hd := (primaryModelCoefficient_denominator_le p hinj b hb' R c H htwo hc hne).trans hmodel
    exact_mod_cast hd

end GridModel

end SquareDifference

namespace SquareDifference

open Finset

section SmallCoordinates

variable {I : Type*} [instFintypeI : Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

noncomputable def smallTupleEquiv :
    ZMod (∏i,smallQuadraticModulus (p i)) ≃+* ∀i,ZMod (smallQuadraticModulus (p i)) :=
  ZMod.prodEquivPi _ (smallQuadraticModuli_pairwise p (fun _ => Fact.out) hinj)

noncomputable def smallCoordinateChar (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I) :
    AddChar (ZMod (smallQuadraticModulus (p i))) ℂ :=
  coordinateChar (((rationalChar b).compAddMonoidHom
    (ZMod.castHom hb (ZMod b.den)).toAddMonoidHom).compAddMonoidHom
      (smallTupleEquiv p hinj).symm.toAddMonoidHom) i

lemma smallCoordinateChar_trivial (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I) (hi : ¬p i∣b.den) :
    smallCoordinateChar p hinj b hb i=1 := by
  apply coordinateChar_inflation_trivial
  have hc := (Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr hi
  unfold smallQuadraticModulus
  split_ifs with h2
  · simpa only [h2,show 2^3=8 by norm_num] using hc.pow_left 3
  · exact hc

lemma smallCoordinateChar_primitive (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I)
    (h2 : p i≠2) (hi : p i∣b.den) :
    (smallCoordinateChar p hinj b hb i).IsPrimitive := by
  apply coordinateChar_inflation_primitive _ hb _ _ (rationalChar_primitive b)
  simpa only [smallQuadraticModulus,ite_eq_right h2] using hi

variable (R : Finset I) (c : ∀i,ZMod (p i))

lemma smallCompleteLocal {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (R : Finset I)
    (c : (i : I) → ZMod (p i)) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,p i=2 → c i=1) (i : I)
    (ψ : AddChar (ZMod (smallQuadraticModulus (p i))) ℂ) :
    (𝔼 x : ZMod (smallQuadraticModulus (p i)),
      localRootWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c i x*
      (1-localSieveWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R i x)*ψ (x^2))=
      if i∈R then ψ (smallRootSquare (p i) (c i)) else unitQuadraticMean ψ := by
  classical
  by_cases hi : i∈R
  · simp only [localRootWeight,localSieveWeight,ite_eq_left hi,sub_zero,mul_one]
    exact small_root_quadratic (c i) (hc i hi) ψ
  · simp only [localRootWeight,localSieveWeight,ite_eq_right hi,one_mul]
    simp_rw [sub_mul,one_mul,expect_sub_distrib]
    exact prime_unit_quadratic_of_eq (prime_dvd_smallQuadraticModulus (p i))
      (ite_eq_right (fun h => hi (htwo i h))) ψ

lemma completeRationalCoefficient_small (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i))
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    completeRationalCoefficient p R c b=
      ∏i, if i∈R then smallCoordinateChar p hinj b hb i (smallRootSquare (p i) (c i))
        else unitQuadraticMean (smallCoordinateChar p hinj b hb i) := by
  classical
  trans periodicMean
    (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))
    (∏i,smallQuadraticModulus (p i))
  · exact completeRationalCoefficient_eq p R c b _
      (NeZero.pos _) (fun i => (prime_dvd_smallQuadraticModulus (p i)).trans
        (dvd_prod_of_mem _ (mem_univ i))) hb
  · trans ∏i,(𝔼 x : ZMod (smallQuadraticModulus (p i)),
      localRootWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c i x*
      (1-localSieveWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R i x)*
      smallCoordinateChar p hinj b hb i (x^2))
    · exact periodicMean_crt_complete p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c (smallTupleEquiv p hinj) b hb
    · apply prod_congr rfl
      intro i _
      exact smallCompleteLocal p R c htwo hc i _

lemma kernelModelCoefficient_small (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H b=
      if ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤H then
        ∏i, if i∈R then smallCoordinateChar p hinj b hb i (smallRootSquare (p i) (c i))
          else unitQuadraticMean (smallCoordinateChar p hinj b hb i)
      else 0 := by
  unfold kernelModelCoefficient
  rw [completeRationalCoefficient_small p hinj R c b hb htwo hc]

end SmallCoordinates

end SquareDifference

open Filter

open scoped Topology

namespace SquareDifference

lemma pow_le_pow_of_one_le (n : ℝ) (hn : 1≤n) {a b : ℝ} (h : a≤b) : n^a≤n^b :=
  Real.rpow_le_rpow_of_exponent_le hn h

lemma kernel_rate_log (n T : ℝ) (hn : 1≤n) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) :
    1+Real.log T ≤18*n^((1:ℝ)/16) := by
  have hn0 : 0<n := by linarith
  have hn1 : 1≤n^((1:ℝ)/16) := Real.one_le_rpow hn (by norm_num)
  have hlog : Real.log n≤16*n^((1:ℝ)/16) := by
    simpa [div_eq_mul_inv,mul_comm] using Real.log_le_rpow_div hn0.le (show 0<(1:ℝ)/16 by norm_num)
  have hl2 : Real.log 2≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (show 0<(2:ℝ) by norm_num)
  have hh := Real.log_le_log hT hTn
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne', Real.log_rpow hn0] at hh
  nlinarith [Real.log_nonneg hn]

lemma kernel_rate_first (n D H T M : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : n^((7:ℝ)/8)≤T+1)
    (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    H*(2*D*H+1)*D*(4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1))*M/n
      ≤3*(4+8*Real.pi)*n^((4:ℝ)/1000-3/8) := by
  have hn0 : 0<n := by linarith
  have hp : 0<n^((7:ℝ)/8) := Real.rpow_pos_of_pos hn0 _
  have hT0 : 0<T+1 := hp.trans_le hT
  have hDH : 1≤D*H := by nlinarith
  have hcost : H*(2*D*H+1)*D≤3*(n^((1:ℝ)/1000))^4 := by
    calc
      _ ≤ H*(3*D*H)*D := by gcongr; nlinarith
      _ = 3*D^2*H^2 := by ring
      _ ≤ 3*(n^((1:ℝ)/1000))^2*(n^((1:ℝ)/1000))^2 := by gcongr
      _ = _ := by ring
  have hdiv : n/(T+1)≤n^((1:ℝ)/8) := by
    calc
      _ ≤ n/n^((7:ℝ)/8) := div_le_div_of_nonneg_left hn0.le hp hT
      _ = n^(1:ℝ)/n^((7:ℝ)/8) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hn0]; norm_num
  have hfreq : 4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1) ≤(4+8*Real.pi)*n^((1:ℝ)/8) := by
    calc
      _ = 4*n^((1:ℝ)/8)+8*Real.pi*(n/(T+1)) := by ring
      _ ≤ 4*n^((1:ℝ)/8)+8*Real.pi*n^((1:ℝ)/8) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (3*(n^((1:ℝ)/1000))^4)*((4+8*Real.pi)*n^((1:ℝ)/8))*n^((1:ℝ)/2)/n := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hcost hfreq (by positivity) (by positivity)) hM hM0
          (by positivity)) hn0.le
    _ = 3*(4+8*Real.pi)*((n^((1:ℝ)/1000))^4*n^((1:ℝ)/8)*n^((1:ℝ)/2)/n^(1:ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_natCast (n^((1:ℝ)/1000)),← Real.rpow_mul hn0.le,
        ← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_rate_sqrt (n T M : ℝ) (hn : 1≤n) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    Real.sqrt (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))
      ≤39*n^((15:ℝ)/32) := by
  have hn0 : 0<n := by linarith
  have hx : 0<n^((1:ℝ)/8) := Real.rpow_pos_of_pos hn0 _
  have h17 : n^((1:ℝ)/2)≤n^((7:ℝ)/8) := pow_le_pow_of_one_le n hn (by norm_num)
  have h79 : n^((7:ℝ)/8)≤n^((15:ℝ)/16) := pow_le_pow_of_one_le n hn (by norm_num)
  have h19 : M≤n^((15:ℝ)/16) := hM.trans (h17.trans h79)
  have hs : M^2/n^((1:ℝ)/8)≤n^((7:ℝ)/8) := by
    calc
      _ ≤ (n^((1:ℝ)/2))^2/n^((1:ℝ)/8) := by gcongr
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le,← Real.rpow_sub hn0]; norm_num
  have hlin : 64*M+8*T≤80*n^((7:ℝ)/8) := by nlinarith [hM.trans h17]
  have hlog := kernel_rate_log n T hn hT hTn
  have hprod : (64*M+8*T)*(1+Real.log T)≤1440*n^((15:ℝ)/16) := by
    calc
      _ ≤ (64*M+8*T)*(18*n^((1:ℝ)/16)) := by gcongr
      _ ≤ (80*n^((7:ℝ)/8))*(18*n^((1:ℝ)/16)) := by gcongr
      _ = _ := by rw [mul_mul_mul_comm,← Real.rpow_add hn0]; norm_num
  have hinside : 5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T)
      ≤1477*n^((15:ℝ)/16) := by
    rw [show 32*M^2/n^((1:ℝ)/8)=32*(M^2/n^((1:ℝ)/8)) by ring]
    linarith [hs.trans h79]
  apply (Real.sqrt_le_left (by positivity)).mpr
  have heq : (39*n^((15:ℝ)/32))^2=1521*n^((15:ℝ)/16) := by
    rw [mul_pow,← Real.rpow_natCast (n^((15:ℝ)/32)),← Real.rpow_mul hn0.le]; norm_num
  rw [heq]
  exact hinside.trans (by gcongr; norm_num)

lemma kernel_rate_second (n D H T M : ℝ) (hn : 1≤n)
    (_ : 0≤D) (hH : 0≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    (D*H)*(4*M/n)*Real.sqrt
      (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))
      ≤156*n^((2:ℝ)/1000-1/32) := by
  have hn0 : 0<n := by linarith
  have hs := kernel_rate_sqrt n T M hn hT hTn hM0 hM
  calc
    _ ≤ (n^((1:ℝ)/1000)*n^((1:ℝ)/1000))*(4*n^((1:ℝ)/2)/n)*
      (39*n^((15:ℝ)/32)) := by gcongr
    _ = 156*(n^((1:ℝ)/1000)*n^((1:ℝ)/1000)*n^((1:ℝ)/2)*n^((15:ℝ)/32)/n^(1:ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_rate_third (n D H T L : ℝ) (hn : 1≤n)
    (_ : 0≤D) (hH : 0≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0≤T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hL : 0≤L) (hLD : L≤2*D*H) :
    L^2*(T*L/n)≤16*n^((6:ℝ)/1000-1/8) := by
  have hn0 : 0<n := by linarith
  have hLn : L≤2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000) := by calc
    _ ≤ 2*D*H := hLD
    _ ≤ _ := by gcongr
  calc
    _ ≤ (2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000))^2*
      ((2*n^((7:ℝ)/8))*(2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000))/n) := by gcongr
    _ = 16*((n^((1:ℝ)/1000))^6*n^((7:ℝ)/8)/n^(1:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_natCast (n^((1:ℝ)/1000)),← Real.rpow_mul hn0.le,
        ← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_all_rates (n D H T L M : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0<T) (hTlo : n^((7:ℝ)/8)≤T+1)
    (hTn : T≤2*n^((7:ℝ)/8)) (hL : 0≤L) (hLD : L≤2*D*H)
    (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    H*(2*D*H+1)*D*(4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1))*M/n+
      (D*H)*(4*M/n)*Real.sqrt
        (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))+
      L^2*(T*L/n)≤(3*(4+8*Real.pi)+156+16)*H^(-(1:ℝ)/3) := by
  have hn0 : 0<n := by linarith
  have hD0 : 0≤D := by linarith
  have hH0 : 0<H := by linarith
  have hh : n^(-(1:ℝ)/3000)≤H^(-(1:ℝ)/3) := by
    have hpow := Real.rpow_le_rpow_of_nonpos hH0 hHn (show -(1:ℝ)/3≤0 by norm_num)
    rw [← Real.rpow_mul hn0.le] at hpow
    norm_num at hpow ⊢
    exact hpow
  have h1 := kernel_rate_first n D H T M hn hD hH hDn hHn hTlo hM0 hM
  have h2 := kernel_rate_second n D H T M hn hD0 hH0.le hDn hHn hT hTn hM0 hM
  have h3 := kernel_rate_third n D H T L hn hD0 hH0.le hDn hHn hT.le hTn hL hLD
  have he1 : n^((4:ℝ)/1000-3/8)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (4:ℝ)/1000-3/8≤ -1/3000)).trans hh
  have he2 : n^((2:ℝ)/1000-1/32)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (2:ℝ)/1000-1/32≤ -1/3000)).trans hh
  have he3 : n^((6:ℝ)/1000-1/8)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (6:ℝ)/1000-1/8≤ -1/3000)).trans hh
  have hfirst : 3*(4+8*Real.pi)*n^((4:ℝ)/1000-3/8)≤3*(4+8*Real.pi)*H^(-(1:ℝ)/3) := by gcongr
  linarith

lemma kernel_parameter_bounds (n D H : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hlarge : 8≤n^((1:ℝ)/16)) :
    let L := ⌈D*H⌉₊
    let T := ⌈n^((7:ℝ)/8)⌉₊
    0<T ∧ 2*L≤T+1 ∧ 8≤n^((1:ℝ)/8) ∧ (L:ℝ)≤n^((1:ℝ)/8) ∧
      D*H≤L ∧ n^((7:ℝ)/8)≤(T:ℝ)+1 ∧ (T:ℝ)≤2*n^((7:ℝ)/8) ∧ (L:ℝ)≤2*D*H := by
  dsimp only
  have hn0 : 0<n := by linarith
  have hDH : 1≤D*H := by nlinarith
  have hDH0 : 0≤D*H := by linarith
  have hL : (⌈D*H⌉₊:ℝ)≤2*D*H := by
    have h := Nat.ceil_lt_add_one hDH0
    nlinarith
  have hm : D*H≤n^((2:ℝ)/1000) := by
    calc
      _ ≤ n^((1:ℝ)/1000)*n^((1:ℝ)/1000) := by gcongr
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hLX : 2*D*H≤n^((1:ℝ)/8) := by
    calc
      _ = 2*(D*H) := by ring
      _ ≤ n^((1:ℝ)/16)*n^((2:ℝ)/1000) := mul_le_mul (by linarith) hm hDH0 (by positivity)
      _ = n^((1:ℝ)/16+2/1000) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := pow_le_pow_of_one_le n hn (by norm_num)
  have hLT : 2*(⌈D*H⌉₊:ℝ)≤n^((7:ℝ)/8) := by
    calc
      _ ≤ 4*(D*H) := by linarith
      _ ≤ n^((1:ℝ)/16)*n^((2:ℝ)/1000) := mul_le_mul (by linarith) hm hDH0 (by positivity)
      _ = n^((1:ℝ)/16+2/1000) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := pow_le_pow_of_one_le n hn (by norm_num)
  have hT : (⌈n^((7:ℝ)/8)⌉₊:ℝ)≤2*n^((7:ℝ)/8) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le ((7:ℝ)/8))
    have h1 := Real.one_le_rpow hn (by norm_num : 0≤(7:ℝ)/8)
    linarith
  refine ⟨Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn0 _),?_,?_,hL.trans hLX,
    Nat.le_ceil _,?_,hT,hL⟩
  · have h := hLT.trans (Nat.le_ceil (n^((7:ℝ)/8)))
    have : 2*⌈D*H⌉₊≤⌈n^((7:ℝ)/8)⌉₊ := by exact_mod_cast h
    omega
  · exact hlarge.trans (pow_le_pow_of_one_le n hn (by norm_num))
  · exact (Nat.le_ceil _).trans (le_add_of_nonneg_right (by norm_num))

lemma exists_kernel_threshold : ∃ N₀ : ℕ, 1≤N₀ ∧ ∀N : ℕ, N₀≤N →
    1≤(N:ℝ) ∧ 8≤(N:ℝ)^((1:ℝ)/16) := by
  have hh : ∀ᶠ N : ℕ in atTop, 8≤(N:ℝ)^((1:ℝ)/16) :=
    ((tendsto_rpow_atTop (by norm_num : 0<(1:ℝ)/16)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 8)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hh
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro N hN
  refine ⟨?_,hT N ((le_max_right _ _).trans hN)⟩
  exact_mod_cast (le_max_left 1 T).trans hN

lemma natural_sqrt_bounds (N : ℕ) (hN : 1≤N) :
    1≤N.sqrt ∧ N.sqrt^2≤N ∧ N<(N.sqrt+1)^2 ∧ (N.sqrt:ℝ)≤(N:ℝ)^((1:ℝ)/2) := by
  refine ⟨Nat.sqrt_pos.mpr (by omega),Nat.sqrt_le' N,Nat.lt_succ_sqrt' N,?_⟩
  rw [← Real.sqrt_eq_rpow]
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact_mod_cast Nat.sqrt_le' N

end SquareDifference

namespace SquareDifference

open Finset

section UniformFinal

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [instFactNatPrimepi : ∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

lemma rootProduct_le_squareModulus {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (R : Finset I) : (∏i∈R,p i)≤rootSquareModulus p R := by
  apply Finset.prod_le_prod
  intro i _
  split_ifs with h
  · omega
  · exact le_rfl

noncomputable def kernelAbsoluteConstant : ℝ := 2^64+3*(4+8*Real.pi)+156+16

lemma actual_kernel_power_error (hinj : Function.Injective p)
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : (rootSquareModulus p R : ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ, (b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0) (α : ℝ) :
    ‖actualSquareTransform p R c H N.sqrt N α-
      actualModelTransform p R c H ⌈(rootSquareModulus p R : ℝ)*H⌉₊ N α‖≤
      kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
  let D : ℝ := rootSquareModulus p R
  have hD1 : 1≤D := by
    dsimp [D]
    exact_mod_cast rootSquareModulus_pos p R
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  obtain ⟨hT,hLT,hX,hLX,hmodel,hTlo,hThi,hLD⟩ :=
    kernel_parameter_bounds (N:ℝ) D H hn hD1 hH hD hHn hlarge
  obtain ⟨hM,hlo,hhi,hMn⟩ := natural_sqrt_bounds N hN
  have hk := actual_kernel_uniform p R c hinj H (by linarith) _ _ _
    hT hLT hX hLX hmodel hcover htwo hc _ N hM hlo hhi α
  have hroot : ((∏i∈R,p i : ℕ):ℝ)≤D := by
    dsimp [D]
    exact_mod_cast rootProduct_le_squareModulus p R
  have hT0 : 0<(⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ) := by exact_mod_cast hT
  have hn0 : 0<(N:ℝ) := by linarith
  have hX0 : 0≤(N:ℝ)^((1:ℝ)/8) := by positivity
  have hnorm := kernel_all_rates (N:ℝ) D H _ _ N.sqrt hn hD1 hH hD hHn hT0
    hTlo hThi (Nat.cast_nonneg _) hLD (Nat.cast_nonneg _) hMn
  have hmono :
      H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ)*
        (4*(N:ℝ)^((1:ℝ)/8)+8*Real.pi*N/((⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ)+1))*N.sqrt/N+
      ((∏i∈R,p i : ℕ)*H)*(4*(N.sqrt:ℝ)/N)*Real.sqrt
        (5*N.sqrt+32*(N.sqrt:ℝ)^2/(N:ℝ)^((1:ℝ)/8)+
          (64*N.sqrt+8*⌈(N:ℝ)^((7:ℝ)/8)⌉₊)*(1+Real.log ⌈(N:ℝ)^((7:ℝ)/8)⌉₊))+
      (⌈D*H⌉₊:ℝ)^2*((⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ)*⌈D*H⌉₊/N)≤
        (3*(4+8*Real.pi)+156+16)*H^(-(1:ℝ)/3) := by
    apply le_trans _ hnorm
    gcongr
  calc
    _ ≤ _ := hk
    _ ≤ kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
      unfold kernelAbsoluteConstant
      linarith

end UniformFinal

end SquareDifference

open Finset Complex

open scoped BigOperators ComplexConjugate

end

end OAI
