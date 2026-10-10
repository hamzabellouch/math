import OAI.Algebra.Drinfeld.Ihara

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace GenericIhara
open AssociativeElimination UniversalEmbedding WordGrading LieGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem above_zero {wt : α → ℕ} (p : A R α) : p∈above wt 0 :=
  mem_space (fun _ _ => Nat.zero_le _)

theorem tree_depth (u : UniversalEmbedding.Tree Bool) :
    u=.leaf false ∨ embed (u.eval : FreeLieAlgebra R Bool)∈above depth 1 := by
  induction u with
  | leaf a =>
    cases a with
    | false => exact Or.inl rfl
    | true =>
      right
      simp only [Tree.eval,AssociativeElimination.embed_of]
      exact word_mem (R:=R) (FreeMonoid.of true) (show 1≤degree depth (FreeMonoid.of true) from le_rfl)
  | node u v hu hv =>
    right
    rcases hu with rfl|hu
    · rcases hv with rfl|hv
      · simp only [Tree.eval,lie_self,map_zero,Submodule.zero_mem]
      · simpa only [Tree.eval,LieHom.map_lie,Nat.zero_add] using above_lie (above_zero (embed (Tree.eval (R:=R) (.leaf false)))) hv
    · simpa only [Tree.eval,LieHom.map_lie,Nat.add_zero] using above_lie hu (above_zero (embed (Tree.eval (R:=R) v)))

theorem homogeneous_depth {n : ℕ} (hn : 1<n) {p : FreeLieAlgebra R Bool}
    (hp : p∈homogeneousLie (fun _ => 1) n) : embed p∈above depth 1 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    rcases tree_depth (R:=R) u with rfl|h
    · simp only [treeDegree_leaf] at hu
      omega
    · exact h
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (above depth 1).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (above depth 1).smul_mem c hp

theorem evalIhara_homogeneous (wt : α → ℕ) (f : α → FreeLieAlgebra R Bool)
    (hf : ∀ a,embed (f a)∈homogeneous (fun _ => 1) (wt a))
    {n : ℕ} {p : FreeLieAlgebra R α} (hp : p∈homogeneousLie wt n) :
    embed (evalIhara f p)∈homogeneous (fun _ => 1) n := by
  have ht : ∀ u : UniversalEmbedding.Tree α,
      embed (evalIhara f u.eval)∈homogeneous (fun _ => 1) (treeDegree wt u) := by
    intro u
    induction u with
    | leaf a => simpa only [Tree.eval,evalIhara_of,treeDegree_leaf] using hf a
    | node u v hu hv =>
      simpa only [Tree.eval,evalIhara_lie,treeDegree_node] using ihara_homogeneous hu hv
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,hu,rfl⟩ := hp; simpa only [hu] using ht u
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (homogeneous _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (homogeneous _ _).smul_mem c hp

theorem evalIhara_depth (f : α → FreeLieAlgebra R Bool)
    (hf : ∀ a,embed (f a)∈above depth 1)
    {n : ℕ} {p : FreeLieAlgebra R α} (hp : p∈homogeneousLie (fun _ => 1) n) :
    embed (evalIhara f p)∈above depth n := by
  have ht : ∀ u : UniversalEmbedding.Tree α,
      embed (evalIhara f u.eval)∈above depth (treeDegree (fun _ => 1) u) := by
    intro u
    induction u with
    | leaf a => simpa only [Tree.eval,evalIhara_of,treeDegree_leaf] using hf a
    | node u v hu hv =>
      simpa only [Tree.eval,evalIhara_lie,treeDegree_node] using ihara_above hu hv
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,hu,rfl⟩ := hp; simpa only [hu] using ht u
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (above _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (above _ _).smul_mem c hp

def depthOneWord (n : ℕ) : FreeMonoid Bool := FreeMonoid.of false^n*FreeMonoid.of true

theorem degree_depthOneWord (n : ℕ) : degree depth (depthOneWord n)=1 := by
  have h : ∀ n,degree depth (FreeMonoid.of false^n)=0 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn => simp [pow_succ,hn,depth]
  simp [depthOneWord,h,depth]

theorem depthOne_zero {p : FreeLieAlgebra R Bool} {r : ℕ} (hr : 1<r)
    (hp : embed p∈above depth r) (n : ℕ) : (embed p).coeff (depthOneWord n)=0 := by
  exact coeff_support hp _ (by rw [degree_depthOneWord]; omega)

end GenericIhara

namespace CutoffDepth
open AssociativeElimination WordGrading
variable {R : Type*} [CommRing R]

abbrev Q (R : Type*) [CommRing R] (N : ℕ) := TruncatedWords.Q (∅ : Set (A R Bool)) N
abbrev quotient (N : ℕ) : A R Bool →ₐ[R] Q R N := TruncatedWords.quotient ∅ N
def gen (N : ℕ) (b : Bool) : Q R N := quotient N (atom b)
abbrev coeff (N : ℕ) (w : FreeMonoid Bool) : Q R N →ₗ[R] R := TruncatedFree.coefficient N w

@[simp] theorem degree_pow (wt : Bool → ℕ) (w : FreeMonoid Bool) (n : ℕ) :
    degree wt (w^n)=n*degree wt w := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ,degree_mul,ih]; ring

@[simp] theorem length_depthOne (m : ℕ) :
    degree TruncatedWords.wt (GenericIhara.depthOneWord m)=m+1 := by
  simp [GenericIhara.depthOneWord,TruncatedWords.wt]

theorem depth_le_length (w : FreeMonoid Bool) :
    degree GenericIhara.depth w≤degree TruncatedWords.wt w := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of b => cases b <;> decide
  | mul u v hu hv => simp only [degree_mul]; omega

def depthSpace (N n : ℕ) : Submodule R (Q R N) :=
  (above GenericIhara.depth n).map (quotient N).toLinearMap

theorem depth_antitone (N : ℕ) : Antitone (depthSpace (R:=R) N) := by
  intro m n h
  exact Submodule.map_mono (space_mono (fun _ hw => le_trans h hw))

theorem depth_one (N : ℕ) : (1:Q R N)∈depthSpace N 0 := by
  exact ⟨1,word_mem 1 (by simp),map_one (quotient N)⟩

theorem depth_mul (N m n : ℕ) {p q : Q R N} (hp : p∈depthSpace N m) (hq : q∈depthSpace N n) :
    p*q∈depthSpace N (m+n) := by
  obtain ⟨a,ha,rfl⟩ := hp
  obtain ⟨b,hb,rfl⟩ := hq
  exact ⟨a*b,above_mul ha hb,map_mul (quotient N) _ _⟩

theorem depth_terminal (N : ℕ) : depthSpace (R:=R) N (N+1)=⊥ := by
  apply eq_bot_iff.mpr
  rintro q ⟨p,hp,rfl⟩
  apply TruncatedWords.quotient_above
  exact space_mono (fun w hw => le_trans hw (depth_le_length w)) hp

theorem gen_depth (N : ℕ) (b : Bool) : gen (R:=R) N b∈depthSpace N (GenericIhara.depth b) := by
  refine ⟨atom b,?_,rfl⟩
  exact word_mem (FreeMonoid.of b) (by simp)

theorem gen_weight (N : ℕ) (b : Bool) : gen (R:=R) N b∈TruncatedWords.filtration ∅ N 1 := by
  refine ⟨atom b,?_,rfl⟩
  exact word_mem (FreeMonoid.of b) (by simp [TruncatedWords.wt])

theorem coeff_zero_of_depth (N n : ℕ) {p : Q R N} (hp : p∈depthSpace N n)
    {w : FreeMonoid Bool} (hw : degree GenericIhara.depth w<n) : coeff N w p=0 := by
  obtain ⟨a,ha,rfl⟩ := hp
  change TruncatedFree.coefficient N w (TruncatedWords.quotient ∅ N a)=0
  rw [TruncatedFree.coefficient_quotient]
  have hz : a.coeff w=0 := coeff_support ha w (not_le.mpr hw)
  split <;> simp only [hz]

theorem left_power_match (i m : ℕ) (v : FreeMonoid Bool) :
    FreeMonoid.of false^i*v=GenericIhara.depthOneWord m ↔
      i ≤ m ∧ v=GenericIhara.depthOneWord (m-i) := by
  induction i generalizing m v with
  | zero => simp
  | succ i ih =>
    cases m with
    | zero =>
      have hn : FreeMonoid.of false^(i+1)*v≠GenericIhara.depthOneWord 0 := by
        intro h
        have hh := congrArg FreeMonoid.toList h
        simp [pow_succ',mul_assoc,GenericIhara.depthOneWord] at hh
      simp [hn]
    | succ m =>
      have he : FreeMonoid.of false^(i+1)*v=GenericIhara.depthOneWord (m+1) ↔
          FreeMonoid.of false^i*v=GenericIhara.depthOneWord m := by
        simp only [pow_succ',GenericIhara.depthOneWord,mul_assoc,mul_left_cancel_iff]
      rw [he,ih]
      simp only [Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub]

theorem coeff_prefix (N i m : ℕ) (hN : m+1≤N) (p : Q R N) :
    coeff N (GenericIhara.depthOneWord m) (gen N false^i*p)=
      if i ≤ m then coeff N (GenericIhara.depthOneWord (m-i)) p else 0 := by
  classical
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective R (TruncatedWords.relations (∅ : Set (A R Bool)) N) p
  change coeff N (GenericIhara.depthOneWord m) (quotient N (atom false)^i*quotient N a)=_
  rw [←map_pow,←map_mul,TruncatedFree.coefficient_quotient,ite_eq_left (by simpa using hN)]
  have he : atom (R:=R) false^i=MonoidAlgebra.single (FreeMonoid.of false^i) 1 := by
    simp [atom,MonoidAlgebra.single_pow]
  rw [he]
  split_ifs with hi
  · rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (GenericIhara.depthOneWord (m-i))
      (fun _ _ => by rw [left_power_match]; simp only [hi,true_and]),one_mul]
    change _=TruncatedFree.coefficient N (GenericIhara.depthOneWord (m-i)) (TruncatedWords.quotient ∅ N a)
    rw [TruncatedFree.coefficient_quotient,ite_eq_left (by simp only [length_depthOne]; omega)]
  · exact MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 a
      (fun v hv => hi ((left_power_match i m v).mp hv).1)

theorem middle_power_match (i j m : ℕ) :
    FreeMonoid.of false^i*FreeMonoid.of true*FreeMonoid.of false^j=GenericIhara.depthOneWord m ↔
      i=m ∧ j=0 := by
  rw [mul_assoc,left_power_match]
  constructor
  · rintro ⟨hi,h⟩
    have hm : m-i=0 := by
      cases he : m-i with
      | zero => rfl
      | succ k =>
        have hh := congrArg FreeMonoid.toList h
        simp [GenericIhara.depthOneWord,he,pow_succ',mul_assoc] at hh
    have him : i=m := by omega
    subst i
    simp only [Nat.sub_self,GenericIhara.depthOneWord,pow_zero,one_mul,mul_eq_left] at h
    have hd := congrArg (degree TruncatedWords.wt) h
    simp only [degree_pow,degree_of,TruncatedWords.wt,mul_one,degree_one] at hd
    exact ⟨rfl,hd⟩
  · rintro ⟨rfl,rfl⟩
    simp [GenericIhara.depthOneWord]

theorem coeff_monomial (N i j m : ℕ) (hN : m+1 ≤ N) :
    coeff N (GenericIhara.depthOneWord m) (gen (R:=R) N false^i*gen N true*gen N false^j)=
      if i=m ∧ j=0 then 1 else 0 := by
  classical
  change coeff N (GenericIhara.depthOneWord m)
    (quotient N (atom false)^i*quotient N (atom true)*quotient N (atom false)^j)=_
  rw [←map_pow,←map_pow,←map_mul,←map_mul,TruncatedFree.coefficient_quotient,
    ite_eq_left (by simpa using hN)]
  simp only [atom,MonoidAlgebra.single_pow,one_pow,MonoidAlgebra.single_mul_single,one_mul]
  simp only [MonoidAlgebra.coeff_single,Finsupp.single_apply,middle_power_match]

theorem coeff_Y_prefix (N i m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) (p : Q R N) :
    coeff N (GenericIhara.depthOneWord m) (gen N true^i*p)=
      if i=0 then coeff N (GenericIhara.depthOneWord m) p else 0 := by
  classical
  cases i with
  | zero => simp
  | succ i =>
    simp only [Nat.succ_ne_zero,↓reduceIte]
    obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective R (TruncatedWords.relations (∅ : Set (A R Bool)) N) p
    change coeff N (GenericIhara.depthOneWord m) (quotient N (atom true)^(i+1)*quotient N a)=0
    rw [←map_pow,←map_mul,TruncatedFree.coefficient_quotient,ite_eq_left (by simpa using hN)]
    have he : atom (R:=R) true^(i+1)=MonoidAlgebra.single (FreeMonoid.of true^(i+1)) 1 := by
      simp [atom,MonoidAlgebra.single_pow]
    rw [he]
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro v hv
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have hh := congrArg FreeMonoid.toList hv
    simp [pow_succ',GenericIhara.depthOneWord,mul_assoc] at hh

end CutoffDepth

section
namespace LogCollar
open MeasureTheory Set Filter
open scoped Topology

theorem intervalIntegrable_of_at_zero {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (h0 : IntegrableAtFilter f (𝓝[>] 0) volume)
    (hc : ContinuousOn f (Ioi 0)) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable f volume 0 b := by
  obtain rfl | hb := hb.eq_or_lt
  · exact IntervalIntegrable.refl
  obtain ⟨s,hs,hi⟩ := h0
  obtain ⟨c,hc0,hcs⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hs
  apply IntervalIntegrable.trans (b:=c)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc0.le).mpr (hi.mono_set hcs)
  · apply ContinuousOn.intervalIntegrable
    exact hc.mono (by
      intro x hx
      have hle : min c b ≤ x := hx.1
      exact lt_of_lt_of_le (lt_min hc0 hb) hle)

theorem log_pow_at_zero (n : ℕ) :
    IntegrableAtFilter (fun x : ℝ => Real.log x ^ n) (𝓝[>] 0) volume := by
  have ho : (fun x : ℝ => ‖Real.log x ^ n‖) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(1/2):ℝ)) := by
    simpa only [norm_pow,Real.norm_eq_abs,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n:ℝ) (by norm_num : (-(1/2):ℝ)<0)).isBigO
  apply ho.of_norm_left.integrableAtFilter
  · exact (Real.measurable_log.pow_const n).stronglyMeasurable.stronglyMeasurableAtFilter
  · refine ⟨Ioc 0 1,Ioc_mem_nhdsGT (by norm_num),?_⟩
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2)))

theorem log_pow (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log x ^ n) volume 0 b := by
  apply intervalIntegrable_of_at_zero (log_pow_at_zero n) _ hb
  exact (Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx)).pow n

end LogCollar

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def gauge (X : A) (s : ℝ) : A := NormedSpace.exp (Real.log s • X)

def regularForm (X Y : A) (s : ℝ) : A :=
  gauge (-X) s * ((s-1)⁻¹ • Y) * gauge X s

theorem exp_smul_finite (X : A) {N : ℕ} (hX : X^(N+1)=0) (t : ℝ) :
    NormedSpace.exp (t • X)=∑ i∈Finset.range (N+1),
      (t^i / (i.factorial : ℝ)) • X^i := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  simp only [smul_pow,smul_smul]
  have hh : ∀ i∉Finset.range (N+1),((i.factorial : ℝ)⁻¹*t^i) • X^i=0 := by
    intro i hi
    have hi : N + 1 ≤ i := Nat.le_of_not_lt (by simpa using hi)
    rw [pow_eq_zero_of_le hi hX,smul_zero]
  rw [tsum_eq_sum hh]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem gauge_finite (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    gauge X s=∑ i∈Finset.range (N+1),
      (Real.log s^i / (i.factorial : ℝ)) • X^i := exp_smul_finite X hX _

variable [CompleteSpace A]

theorem gauge_neg_mul (X : A) (s : ℝ) : gauge (-X) s*gauge X s=1 := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_neg,←NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,neg_add_cancel,
    NormedSpace.exp_zero]

theorem gauge_mul_neg (X : A) (s : ℝ) : gauge X s*gauge (-X) s=1 := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_neg,←NormedSpace.exp_add_of_commute (Commute.refl _).neg_right,add_neg_cancel,
    NormedSpace.exp_zero]

theorem gauge_derivative (X : A) {s : ℝ} (hs : s≠0) :
    HasDerivAt (gauge X) (s⁻¹ • (X*gauge X s)) s := by
  exact (hasDerivAt_exp_smul_const' X (Real.log s)).scomp s (Real.hasDerivAt_log hs)

omit [CompleteSpace A] in
theorem regularForm_finite (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    regularForm X Y s=∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j) := by
  have hnX : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  unfold regularForm
  rw [gauge_finite (-X) hnX,gauge_finite X hX]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  have hp : (-1:A)^i*X^i*Y*X^j=(-1:ℝ)^i • (X^i*Y*X^j) := by
    simp only [Algebra.smul_def,map_pow,map_neg,map_one]
    noncomm_ring
  rw [hp,smul_smul]
  congr 1
  rw [pow_add]
  ring

omit [CompleteSpace A] in

theorem regularForm_integrable (X Y : A) {N : ℕ} (hX : X^(N+1)=0)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (regularForm X Y) volume 0 b := by
  have hc : ContinuousOn (fun s : ℝ => (s-1)⁻¹) (uIcc 0 b) := by
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact ne_of_lt (sub_neg.mpr (lt_of_le_of_lt hs.2 hb1))
  have h : regularForm X Y = fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j) := by
    funext s
    exact regularForm_finite X Y hX s
  rw [h]
  have hh (i j : ℕ) : IntervalIntegrable (fun s =>
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) volume 0 b :=
    (((LogCollar.log_pow (i+j) hb).mul_const _).mul_continuousOn hc).smul_continuousOn
      continuousOn_const
  have hz := IntervalIntegrable.sum (ε:=A) (Finset.range (N+1))
    (fun i _ => IntervalIntegrable.sum (ε:=A) (Finset.range (N+1)) (fun j _ => hh i j))
  have he : (∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),fun s =>
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) =
      (fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      ((Real.log s)^(i+j) * ((-1:ℝ)^i / ((i.factorial:ℝ)*(j.factorial:ℝ))) * (s-1)⁻¹) • (X^i*Y*X^j)) := by
    ext s
    simp only [Finset.sum_apply]
  rw [he] at hz
  exact hz

theorem regularForm_continuous (X Y : A) {b : ℝ} (hb : b ≤ 1) :
    ContinuousOn (regularForm X Y) (Ioo 0 b) := by
  intro s hs
  have hg : ∀ Z : A, ContinuousAt (gauge Z) s := fun Z =>
    (gauge_derivative Z (ne_of_gt hs.1)).continuousAt
  have hinv : ContinuousAt (fun s : ℝ => (s-1)⁻¹) s := by
    apply (continuousAt_id.sub continuousAt_const).inv₀
    exact ne_of_lt (sub_neg.mpr (lt_of_lt_of_le hs.2 hb))
  exact (((hg (-X)).mul (hinv.smul continuousAt_const)).mul (hg X)).continuousWithinAt

omit [CompleteSpace A] in
theorem regularForm_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    regularForm X Y s ∈ F.space 1 := by
  rw [regularForm_finite X Y (pow_cutoff_eq_zero F hX)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply F.antitone (by omega : 1 ≤ i+1+j)
  exact F.mul_mem (i+1) j (F.mul_mem i 1 (pow_mem F hX i) hY) (pow_mem F hX j)

def normalizedSolution (F : NilpotentFiltration A) (X Y : A) (s : ℝ) : A :=
  gauge X s * transport (regularForm X Y) 0 F.cutoff s

variable [FiniteDimensional ℝ A]

theorem normalizedSolution_derivative (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {b s : ℝ}
    (hb : b < 1) (hs : s ∈ Ioo 0 b) :
    HasDerivAt (normalizedSolution F X Y)
      ((s⁻¹ • X + (s-1)⁻¹ • Y) * normalizedSolution F X Y s) s := by
  have hreg := regularForm_integrable X Y (pow_cutoff_eq_zero F hX)
    (le_trans hs.1.le hs.2.le) hb
  have hsol := derivative_nilpotent_transport F (regularForm_mem F hX hY)
    hreg (regularForm_continuous X Y hb.le) hs
  apply ((gauge_derivative X (ne_of_gt hs.1)).mul hsol).congr_deriv
  let P := transport (regularForm X Y) 0 F.cutoff s
  change (s⁻¹ • (X*gauge X s))*P +
    gauge X s*((gauge (-X) s*((s-1)⁻¹ • Y)*gauge X s)*P) =
    (s⁻¹ • X+(s-1)⁻¹ • Y)*(gauge X s*P)
  rw [←mul_assoc (gauge X s),←mul_assoc (gauge X s),←mul_assoc (gauge X s),gauge_mul_neg,one_mul]
  simp only [add_mul,smul_mul_assoc,mul_assoc]

omit [FiniteDimensional ℝ A] in
theorem normalizedSolution_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (fun s => gauge (-X) s * normalizedSolution F X Y s)
      (𝓝[>] 0) (𝓝 (1:A)) := by
  have hh : (fun s => gauge (-X) s * normalizedSolution F X Y s) =
      transport (regularForm X Y) 0 F.cutoff := by
    funext s
    simp only [normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul]
  rw [hh]
  have h := collar_limit (regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hb.le hb1) F.cutoff
  rw [uIcc_of_le hb.le] at h
  rw [nhdsWithin_Icc_eq_nhdsGE hb] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

end KZCollar

namespace FinitePicard
open MeasureTheory Set intervalIntegral
open scoped Ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [FiniteDimensional ℝ A]

theorem transport_sub_one_mem (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) (N : ℕ) :
    transport Ω a N t-1 ∈ F.space 1 := by
  simp only [transport,Finset.sum_range_succ',term_zero,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro n hn
  exact F.antitone (by omega : 1 ≤ n+1) (term_mem F hΩ a (n+1) t)

theorem transport_isUnit (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) (N : ℕ) :
    IsUnit (transport Ω a N t) := by
  have hn : IsNilpotent (transport Ω a N t-1) :=
    ⟨F.cutoff+1,pow_cutoff_eq_zero F (transport_sub_one_mem F hΩ a t N)⟩
  simpa only [sub_add_cancel] using hn.isUnit_add_one

omit [FiniteDimensional ℝ A] in
theorem inverse_derivative [CompleteSpace A] {f : ℝ → A} {f' : A} {s : ℝ}
    (hf : HasDerivAt f f' s) (hu : IsUnit (f s)) :
    HasDerivAt (fun s => Ring.inverse (f s)) (-(Ring.inverse (f s)*f'*Ring.inverse (f s))) s := by
  have h := hasFDerivAt_ringInverse (𝕜:=ℝ) hu.unit
  rw [hu.unit_spec] at h
  have hh := h.comp_hasDerivAt s hf
  simpa only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    ←Ring.inverse_of_isUnit hu] using! hh

omit [FiniteDimensional ℝ A] in

theorem transition_derivative [CompleteSpace A] {f g Ω : ℝ → A} {s : ℝ}
    (hf : HasDerivAt f (Ω s*f s) s) (hg : HasDerivAt g (Ω s*g s) s)
    (hu : IsUnit (f s)) :
    HasDerivAt (fun s => Ring.inverse (f s)*g s) 0 s := by
  apply ((inverse_derivative hf hu).mul hg).congr_deriv
  simp only [mul_assoc,neg_mul]
  rw [←mul_assoc (f s),Ring.mul_inverse_cancel _ hu,one_mul,neg_add_cancel]

omit [FiniteDimensional ℝ A] in
theorem transition_constant [CompleteSpace A] {f g Ω : ℝ → A} {a b u v : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hg : ∀ s ∈ Ioo a b, HasDerivAt g (Ω s*g s) s)
    (hu : ∀ s ∈ Ioo a b, IsUnit (f s)) (huv : u ∈ Ioo a b) (hvv : v ∈ Ioo a b) :
    Ring.inverse (f u)*g u=Ring.inverse (f v)*g v := by
  have hh : ∀ s ∈ Ioo a b, HasDerivAt (fun s => Ring.inverse (f s)*g s) 0 s :=
    fun s hs => transition_derivative (hf s hs) (hg s hs) (hu s hs)
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hh s hs).differentiableAt.differentiableWithinAt) _ huv hvv
  intro s hs
  exact (hh s hs).deriv

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology Ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def bulkForm (X Y : A) (s : ℝ) : A := s⁻¹ • X+(s-1)⁻¹ • Y

def gaugeUnit (X : A) (s : ℝ) : Aˣ where
  val := gauge X s
  inv := gauge (-X) s
  val_inv := gauge_mul_neg X s
  inv_val := gauge_neg_mul X s

variable [FiniteDimensional ℝ A]

theorem normalizedSolution_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    IsUnit (normalizedSolution F X Y s) :=
  (gaugeUnit X s).isUnit.mul (transport_isUnit F (regularForm_mem F hX hY) 0 s F.cutoff)

theorem normalizedSolution_derivative_on (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt (normalizedSolution F X Y)
      (bulkForm X Y s * normalizedSolution F X Y s) s := by
  apply normalizedSolution_derivative F hX hY (b:=(s+1)/2)
  · linarith [hs.2]
  · exact ⟨hs.1,by linarith [hs.2]⟩

def rightSolution (F : NilpotentFiltration A) (X Y : A) (s : ℝ) : A :=
  normalizedSolution F Y X (1-s)

theorem rightSolution_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    IsUnit (rightSolution F X Y s) := normalizedSolution_isUnit F hY hX (1-s)

theorem rightSolution_derivative (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt (rightSolution F X Y)
      (bulkForm X Y s*rightSolution F X Y s) s := by
  have ht : 1-s ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (normalizedSolution_derivative_on F hY hX ht).scomp s
    ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s))
  apply hd.congr_deriv
  change (0-1:ℝ) • (bulkForm Y X (1-s)*rightSolution F X Y s) = _
  have h1 : 1-s= -(s-1) := by ring
  have h2 : 1-s-1= -s := by ring
  dsimp only [bulkForm]
  rw [h2,h1]
  simp only [inv_neg,zero_sub,neg_smul,one_smul,neg_add_rev,neg_neg,neg_mul,add_mul]

def associator (F : NilpotentFiltration A) (X Y : A) : A :=
  Ring.inverse (rightSolution F X Y (1/2))*normalizedSolution F X Y (1/2)

theorem associator_is_transition (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    Ring.inverse (rightSolution F X Y s)*normalizedSolution F X Y s=associator F X Y := by
  exact transition_constant (fun _ ht => rightSolution_derivative F hX hY ht)
    (fun _ ht => normalizedSolution_derivative_on F hX hY ht)
    (fun t _ => rightSolution_isUnit F hX hY t) hs (by constructor <;> norm_num)

theorem left_eq_right_mul_associator (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    normalizedSolution F X Y s=rightSolution F X Y s*associator F X Y := by
  rw [←associator_is_transition F hX hY hs]
  exact (Ring.mul_inverse_cancel_left _ _ (rightSolution_isUnit F hX hY s)).symm

theorem associator_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) : IsUnit (associator F X Y) := by
  apply IsUnit.mul
  · exact (rightSolution_isUnit F hX hY (1/2)).ringInverse
  · exact normalizedSolution_isUnit F hX hY (1/2)

end KZCollar

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_term (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (term Ω a N t)=term (fun s => f (Ω s)) a N t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rw [term_succ,term_succ]
    let fc := f.toLinearMap.toContinuousLinearMap
    have hi' : IntervalIntegrable (fun s => Ω s * term Ω a N s) volume a t :=
      (hi.mul_continuousOn (continuousOn_term hi N)).mono_set (uIcc_subset_uIcc_left ht)
    change fc (∫ s in a..t, Ω s * term Ω a N s)=_
    rw [←fc.intervalIntegral_comp_comm hi']
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ uIcc a b := uIcc_subset_uIcc_left ht hs
    change f (Ω s*term Ω a N s)=f (Ω s)*term (fun s => f (Ω s)) a N s
    rw [map_mul,ih hst]

theorem map_transport (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (transport Ω a N t)=transport (fun s => f (Ω s)) a N t := by
  simp only [transport,map_sum]
  exact Finset.sum_congr rfl (fun n _ => map_term f hi n ht)

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

theorem map_gauge (f : A →ₐ[ℝ] B) (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (gauge X s)=gauge (f X) s := by
  have hY : (f X)^(N+1)=0 := by rw [←map_pow,hX,map_zero]
  rw [gauge_finite X hX,gauge_finite (f X) hY]
  simp only [map_sum,map_smul,map_pow]

theorem map_regularForm (f : A →ₐ[ℝ] B) (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (regularForm X Y s)=regularForm (f X) (f Y) s := by
  have hN : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  simp only [regularForm,map_mul,map_smul,map_gauge f X hX,map_gauge f (-X) hN,map_neg]

variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_normalizedSolution (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X : A} (hX : X ∈ F.space 1) (Y : A) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  have hi := regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hs hs1
  simp only [normalizedSolution,map_mul,map_gauge f X (pow_cutoff_eq_zero F hX)]
  rw [map_transport f hi F.cutoff right_mem_uIcc,hN]
  have hh : (fun s => f (regularForm X Y s))=regularForm (f X) (f Y) := by
    funext s
    exact map_regularForm f X Y (pow_cutoff_eq_zero F hX) s
  rw [hh]

omit [FiniteDimensional ℝ A] [CompleteSpace B] in
theorem map_unit_inverse (f : A →ₐ[ℝ] B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x)=Ring.inverse (f x) := by
  calc
    f (Ring.inverse x)=f (Ring.inverse x)*(f x*Ring.inverse (f x)) := by
      rw [Ring.mul_inverse_cancel _ (hx.map f),mul_one]
    _ = (f (Ring.inverse x)*f x)*Ring.inverse (f x) := (mul_assoc _ _ _).symm
    _ = Ring.inverse (f x) := by rw [←map_mul,Ring.inverse_mul_cancel _ hx,map_one,one_mul]

variable [CompleteSpace A]

theorem map_associator (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X Y : A} (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  rw [associator,map_mul,map_unit_inverse f (rightSolution_isUnit F hX hY (1/2))]
  unfold rightSolution
  rw [map_normalizedSolution f F G hN hY X (by norm_num) (by norm_num),
    map_normalizedSolution f F G hN hX Y (by norm_num) (by norm_num)]
  rfl

end KZCollar

namespace FinitePicard
open MeasureTheory Set
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem transition_constant_closed {f g Ω : ℝ → A} {a b u v : ℝ} (hab : a < b)
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hg : ∀ s ∈ Ioo a b, HasDerivAt g (Ω s*g s) s)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hu : ∀ s ∈ Icc a b, IsUnit (f s)) (huv : u ∈ Icc a b) (hvv : v ∈ Icc a b) :
    Ring.inverse (f u)*g u=Ring.inverse (f v)*g v := by
  let c := (a+b)/2
  have hc : c ∈ Ioo a b := ⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩
  have he : EqOn (fun s => Ring.inverse (f s)*g s)
      (fun _ => Ring.inverse (f c)*g c) (Ioo a b) := by
    intro s hs
    exact transition_constant hf hg (fun s hs => hu s ⟨hs.1.le,hs.2.le⟩) hs hc
  have hi : ContinuousOn (fun s => Ring.inverse (f s)) (Icc a b) := by
    intro s hs
    have hh := NormedRing.inverse_continuousAt (hu s hs).unit
    rw [(hu s hs).unit_spec] at hh
    exact hh.comp_continuousWithinAt (hfc s hs)
  have he' := he.of_subset_closure (hi.mul hgc) continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  exact (he' huv).trans (he' hvv).symm

variable [FiniteDimensional ℝ A]

theorem transport_eq_fundamental (F : NilpotentFiltration A) {Ω f : ℝ → A}
    (hΩ : ∀ s, Ω s ∈ F.space 1) {a b : ℝ} (hab : a < b)
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hfc : ContinuousOn f (Icc a b)) (hu : ∀ s ∈ Icc a b, IsUnit (f s)) :
    transport Ω a F.cutoff b=f b*Ring.inverse (f a) := by
  have hcont := continuousOn_transport hi F.cutoff
  rw [uIcc_of_le hab.le] at hcont
  have h := transition_constant_closed hab hf
    (fun s hs => derivative_nilpotent_transport F hΩ hi hc hs)
    hfc hcont hu (right_mem_Icc.mpr hab.le) (left_mem_Icc.mpr hab.le)
  rw [transport_base,mul_one] at h
  calc
    transport Ω a F.cutoff b = f b*(Ring.inverse (f b)*transport Ω a F.cutoff b) := by
      rw [←mul_assoc,Ring.mul_inverse_cancel _ (hu b (right_mem_Icc.mpr hab.le)),one_mul]
    _ = f b*Ring.inverse (f a) := congrArg (f b*·) h

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem bulkForm_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    bulkForm X Y s ∈ F.space 1 := (F.space 1).add_mem
      ((F.space 1).smul_mem _ hX) ((F.space 1).smul_mem _ hY)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem bulkForm_continuous (X Y : A) : ContinuousOn (bulkForm X Y) (Ioo 0 1) := by
  apply ContinuousOn.add
  · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt hs.1)).smul continuousOn_const
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun s hs => ne_of_lt (sub_neg.mpr hs.2))).smul continuousOn_const

theorem bulk_transport (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {r t : ℝ}
    (hr : 0 < r) (hrt : r < t) (ht : t < 1) :
    transport (bulkForm X Y) r F.cutoff t =
      normalizedSolution F X Y t * Ring.inverse (normalizedSolution F X Y r) := by
  have hs : Icc r t ⊆ Ioo (0:ℝ) 1 := fun s hs =>
    ⟨lt_of_lt_of_le hr hs.1,lt_of_le_of_lt hs.2 ht⟩
  have hc := (bulkForm_continuous X Y).mono hs
  apply transport_eq_fundamental F (bulkForm_mem F hX hY) hrt
  · exact hc.intervalIntegrable_of_Icc hrt.le
  · exact hc.mono Ioo_subset_Icc_self
  · exact fun s h => normalizedSolution_derivative_on F hX hY (hs ⟨h.1.le,h.2.le⟩)
  · exact fun s h => (normalizedSolution_derivative_on F hX hY (hs h)).continuousAt.continuousWithinAt
  · exact fun s _ => normalizedSolution_isUnit F hX hY s

def regularizedBulk (F : NilpotentFiltration A) (X Y : A) (r : ℝ) : A :=
  gauge (-Y) r * transport (bulkForm X Y) r F.cutoff (1-r) * gauge X r

theorem regularizedBulk_eq (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1/2) :
    regularizedBulk F X Y r =
      transport (regularForm Y X) 0 F.cutoff r * associator F X Y *
        Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
  have hu := transport_isUnit F (regularForm_mem F hX hY) 0 r F.cutoff
  have hg : Ring.inverse (normalizedSolution F X Y r)*gauge X r =
      Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
    rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (normalizedSolution_isUnit F hX hY r)]
    simp only [normalizedSolution,mul_assoc,Ring.mul_inverse_cancel _ hu,mul_one]
  have ht : 1-r ∈ Ioo (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  unfold regularizedBulk
  rw [bulk_transport F hX hY hr (by linarith) ht.2,
    left_eq_right_mul_associator F hX hY ht]
  unfold rightSolution
  have her : 1-(1-r)=r := by ring
  rw [her]
  simp only [normalizedSolution, mul_assoc] at hg ⊢
  rw [←mul_assoc (gauge (-Y) r) (gauge Y r),gauge_neg_mul,one_mul]
  rw [hg]

omit [FiniteDimensional ℝ A] in
theorem regularTransport_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) :
    Tendsto (transport (regularForm X Y) 0 F.cutoff) (𝓝[>] 0) (𝓝 (1:A)) := by
  have h := normalizedSolution_limit (Y:=Y) F hX (b:=1/2) (by norm_num) (by norm_num)
  simpa only [normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul] using h

theorem regularizedBulk_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) :
    Tendsto (regularizedBulk F X Y) (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h0 := regularTransport_limit (Y:=Y) F hX
  have h1 := regularTransport_limit (Y:=X) F hY
  have hi : Tendsto (fun r => Ring.inverse (transport (regularForm X Y) 0 F.cutoff r))
      (𝓝[>] 0) (𝓝 (1:A)) := by
    have h := (NormedRing.inverse_continuousAt (1:Aˣ)).tendsto.comp h0
    simpa only [Units.val_one,Ring.inverse_one,Function.comp_def] using! h
  have h := (h1.mul (tendsto_const_nhds (x:=associator F X Y))).mul hi
  simp only [one_mul,mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with r hr hr1
  exact (regularizedBulk_eq F hX hY hr hr1).symm

end KZCollar
end

namespace DepthIntegral
open MeasureTheory Set Filter intervalIntegral
open scoped Topology

def kernel (m : ℕ) (s : ℝ) : ℝ := (-Real.log s)^m/(1-s)

theorem kernel_left (m : ℕ) {b : ℝ} (h0 : 0≤b) (h1 : b<1) :
    IntervalIntegrable (kernel m) volume 0 b := by
  have hl := (LogCollar.log_pow m h0).const_mul ((-1:ℝ)^m)
  have hc : ContinuousOn (fun s : ℝ => (1-s)⁻¹) (uIcc 0 b) := by
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro s hs
    rw [uIcc_of_le h0] at hs
    exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hs.2 h1))
  have he : kernel m=(fun s => ((-1:ℝ)^m*Real.log s^m)*(1-s)⁻¹) := by
    funext s
    unfold kernel
    rw [neg_pow,div_eq_mul_inv]
  rw [he]
  exact hl.mul_continuousOn hc

theorem slope_continuous : ContinuousOn (dslope Real.log 1) (Ioi 0) := by
  apply (continuousOn_dslope (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))).mpr
  exact ⟨Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx),
    (Real.hasDerivAt_log one_ne_zero).differentiableAt⟩

theorem kernel_eq (m : ℕ) {s : ℝ} (hs : s≠1) :
    kernel (m+1) s=(-Real.log s)^m*dslope Real.log 1 s := by
  rw [dslope_of_ne _ hs]
  simp only [slope,Real.log_one,vsub_eq_sub,sub_zero,smul_eq_mul]
  unfold kernel
  rw [pow_succ]
  field_simp
  ring

theorem kernel_integrable (m : ℕ) (hm : 0 < m) :
    IntervalIntegrable (kernel m) volume 0 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  apply (kernel_left (k+1) (b:=1/2) (by norm_num) (by norm_num)).trans
  have hc : ContinuousOn (fun s => (-Real.log s)^k*dslope Real.log 1 s) (Ioi 0) :=
    ((Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx)).neg.pow k).mul slope_continuous
  have hi : IntervalIntegrable (fun s => (-Real.log s)^k*dslope Real.log 1 s) volume (1/2) 1 := (hc.mono (show uIcc (1/2:ℝ) 1⊆Ioi 0 by
    rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤1)]
    intro s hs
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hs.1)).intervalIntegrable
  apply hi.congr_uIoo
  intro s hs
  rw [uIoo_of_lt (by norm_num : (1/2:ℝ)<1)] at hs
  exact (kernel_eq k (ne_of_lt hs.2)).symm

theorem kernel_pos (m : ℕ) {s : ℝ} (hs : s∈Ioo 0 1) : 0<kernel m s := by
  apply div_pos
  · exact pow_pos (neg_pos.mpr (Real.log_neg hs.1 hs.2)) m
  · exact sub_pos.mpr hs.2

theorem integral_pos (m : ℕ) (hm : 0 < m) : 0 < ∫ s in (0:ℝ)..1,kernel m s :=
  intervalIntegral_pos_of_pos_on (kernel_integrable m hm)
    (fun _ hs => kernel_pos m hs) (by norm_num)

theorem coefficient_ne_zero (m : ℕ) (hm : 0 < m) :
    -(1/(m.factorial:ℝ))*(∫ s in (0:ℝ)..1,kernel m s)≠0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))
  · exact ne_of_gt (integral_pos m hm)

theorem integral_zero {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    (∫ t in (0:ℝ)..s,kernel 0 t)=-Real.log (1-s) := by
  have hd (t : ℝ) (ht : t∈uIcc 0 s) :
      HasDerivAt (fun t : ℝ => -Real.log (1-t)) (kernel 0 t) t := by
    rw [uIcc_of_le h0] at ht
    have hne : 1-t≠0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 h1))
    have h := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log hne).neg
    simpa only [kernel,pow_zero,zero_sub,neg_div,one_div,neg_neg,Pi.sub_apply,Pi.neg_apply,id_eq] using! h
  have h := integral_eq_sub_of_hasDerivAt hd (kernel_left 0 h0 h1)
  simpa using h

theorem integral_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (fun s => ∫ t in (0:ℝ)..s,kernel m t) (𝓝[<] 1)
      (𝓝 (∫ t in (0:ℝ)..1,kernel m t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (kernel_integrable m hm) left_mem_uIcc
  have hh := hc 1 right_mem_uIcc
  change Tendsto _ (𝓝[uIcc 0 1] 1) _ at hh
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0:ℝ)<1)] at hh
  exact hh.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem one_sub_limit : Tendsto (fun s : ℝ => 1-s) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun s : ℝ => 1-s) := continuous_const.sub continuous_id
    have hh : Tendsto (fun s : ℝ => 1-s) (𝓝 (1:ℝ)) (𝓝 (1-1:ℝ)) := hc.tendsto 1
    simpa only [sub_self] using hh.mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < 1-s
    exact sub_pos.mpr (show s < 1 from hs)

theorem log_endpoint_product (m : ℕ) (hm : 0 < m) :
    Tendsto (fun s : ℝ => Real.log s^m*Real.log (1-s)) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h0 : Tendsto (fun s : ℝ => Real.log (1-s)*(1-s)) (𝓝[<] 1) (𝓝 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<1)).comp one_sub_limit
  have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  have hd := (continuousAt_dslope_same.mpr (Real.hasDerivAt_log one_ne_zero).differentiableAt).tendsto.mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  have hh := ((hl.pow k).neg.mul hd).mul h0
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards with s
  have he : (s-1)*dslope Real.log 1 s=Real.log s := by
    simpa only [smul_eq_mul,Real.log_one,sub_zero] using sub_smul_dslope Real.log 1 s
  change -(Real.log s^k)*dslope Real.log 1 s*(Real.log (1-s)*(1-s))=Real.log s^(k+1)*Real.log (1-s)
  rw [pow_succ]
  calc
    _ = Real.log s^k*((s-1)*dslope Real.log 1 s)*Real.log (1-s) := by ring
    _ = _ := by rw [he]

end DepthIntegral

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

instance normedRing (N : ℕ) : NormedRing (Q ℝ N) := FiniteAlgebraNorm.normedRing _
instance normedAlgebra (N : ℕ) : NormedAlgebra ℝ (Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def weight (N : ℕ) : NilpotentFiltration (Q ℝ N) where
  space := TruncatedWords.filtration ∅ N
  antitone := TruncatedWords.filtration_antitone ∅ N
  one_mem := TruncatedWords.filtration_one ∅ N
  mul_mem := TruncatedWords.filtration_mul ∅ N
  cutoff := N
  terminal := TruncatedWords.filtration_terminal ∅ N

def depth (N : ℕ) : NilpotentFiltration (Q ℝ N) where
  space := depthSpace N
  antitone := depth_antitone N
  one_mem := depth_one N
  mul_mem := depth_mul N
  cutoff := N
  terminal := depth_terminal N

abbrev X (N : ℕ) : Q ℝ N := gen N false
abbrev Y (N : ℕ) : Q ℝ N := gen N true
abbrev c (N m : ℕ) : Q ℝ N →ₗ[ℝ] ℝ := coeff N (GenericIhara.depthOneWord m)

theorem X_nilpotent (N : ℕ) : X N^(N+1)=0 := pow_cutoff_eq_zero (weight N) (gen_weight N false)

theorem X_pow_depth (N i : ℕ) : X N^i∈depthSpace N 0 := by
  induction i with
  | zero => simpa using depth_one N
  | succ i ih => simpa only [pow_succ,Nat.zero_add] using depth_mul N 0 0 ih (gen_depth N false)

theorem regularForm_depth (N : ℕ) (s : ℝ) : regularForm (X N) (Y N) s∈depthSpace N 1 := by
  rw [regularForm_finite _ _ (X_nilpotent N)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact depth_mul N 1 0 (depth_mul N 0 1 (X_pow_depth N i) (gen_depth N true)) (X_pow_depth N j)

theorem coeff_one (N m : ℕ) : c N m 1=0 := by
  rw [←(quotient (R:=ℝ) N).map_one]
  change TruncatedFree.coefficient N _ (TruncatedWords.quotient (∅ : Set (AssociativeElimination.A ℝ Bool)) N (1 : AssociativeElimination.A ℝ Bool))=0
  rw [TruncatedFree.coefficient_quotient]
  have hn : GenericIhara.depthOneWord m≠1 := by
    intro h
    have hh := congrArg (WordGrading.degree TruncatedWords.wt) h
    simp only [length_depthOne,WordGrading.degree_one] at hh
    omega
  classical
  simp [MonoidAlgebra.one_def,MonoidAlgebra.coeff_single,hn]

theorem coeff_high_term (N m k : ℕ) (hk : 2 ≤ k) (s : ℝ) :
    c N m (term (regularForm (X N) (Y N)) 0 k s)=0 := by
  apply coeff_zero_of_depth N k (term_mem (depth N) (regularForm_depth N) 0 k s)
  simpa [GenericIhara.depthOneWord,GenericIhara.depth] using (show 1 < k by omega)

theorem coeff_form (N m : ℕ) (hN : m+1 ≤ N) (s : ℝ) :
    c N m (regularForm (X N) (Y N) s)=-(1/(m.factorial:ℝ))*DepthIntegral.kernel m s := by
  rw [regularForm_finite _ _ (X_nilpotent N),map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,c,coeff_monomial N _ _ m hN]
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single 0]
    · simp only [and_self,↓reduceIte,mul_one,Nat.factorial_zero,Nat.cast_one,add_zero]
      unfold DepthIntegral.kernel
      rw [neg_pow,show s-1= -(1-s) by ring,inv_neg,div_eq_mul_inv]
      ring
    · intro j hj hj0
      simp only [hj0,and_false,↓reduceIte,mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ N)))
  · intro i hi him
    simp only [him,false_and,↓reduceIte,mul_zero,Finset.sum_const_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem coeff_first_term (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (term (regularForm (X N) (Y N)) 0 1 s)=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel m t) := by
  simp only [term_succ,term_zero,mul_one]
  change (c N m).toContinuousLinearMap (∫ t in (0:ℝ)..s,regularForm (X N) (Y N) t)=_
  rw [←(c N m).toContinuousLinearMap.intervalIntegral_comp_comm
    (regularForm_integrable _ _ (X_nilpotent N) h0 h1)]
  change (∫ t in (0:ℝ)..s,c N m (regularForm (X N) (Y N) t))=_
  simp only [coeff_form N m hN]
  exact intervalIntegral.integral_const_mul _ _

theorem coeff_transport (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (transport (regularForm (X N) (Y N)) 0 N s)=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel m t) := by
  rw [transport,map_sum,Finset.sum_eq_single 1]
  · exact coeff_first_term N m hN h0 h1
  · intro k hk hn
    by_cases hz : k=0
    · subst k; simp only [term_zero,coeff_one]
    · exact coeff_high_term N m k (by omega) s
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

end CutoffKZ

namespace KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

 theorem gauge_sub_one_mem (F : NilpotentFiltration A) {X : A}
    (hX : X∈F.space 1) (s : ℝ) : gauge X s-1∈F.space 1 := by
  rw [gauge_finite X (pow_cutoff_eq_zero F hX),Finset.sum_range_succ']
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_smul,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  exact (F.space 1).smul_mem _ (F.antitone (by omega : 1 ≤ i+1) (pow_mem F hX (i+1)))

 theorem product_sub_one_mem (F : NilpotentFiltration A) {u v : A}
    (hu : u-1∈F.space 1) (hv : v-1∈F.space 1) : u*v-1∈F.space 1 := by
  have hv0 : v∈F.space 0 := by
    simpa only [sub_add_cancel] using (F.space 0).add_mem (F.antitone (by omega : 0≤1) hv) F.one_mem
  have hh := (F.space 1).add_mem (F.mul_mem 1 0 hu hv0) hv
  simpa only [sub_mul,one_mul,sub_add_sub_cancel] using hh

 theorem inverse_sub_one_mem (F : NilpotentFiltration A) {u : A}
    (hF : F.space 0=⊤) (hu : u-1∈F.space 1) (hunit : IsUnit u) :
    Ring.inverse u-1∈F.space 1 := by
  have hi : Ring.inverse u∈F.space 0 := by rw [hF]; trivial
  have hh := F.mul_mem 0 1 hi hu
  have he : Ring.inverse u*(u-1)= -(Ring.inverse u-1) := by
    rw [mul_sub,Ring.inverse_mul_cancel _ hunit,mul_one,neg_sub]
  rw [he] at hh
  exact (F.space 1).neg_mem_iff.mp hh

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem normalizedSolution_sub_one_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (s : ℝ) :
    normalizedSolution F X Y s-1∈F.space 1 :=
  product_sub_one_mem F (gauge_sub_one_mem F hX s)
    (transport_sub_one_mem F (regularForm_mem F hX hY) 0 s F.cutoff)

 theorem associator_sub_one_mem (F : NilpotentFiltration A) {X Y : A}
    (hF : F.space 0=⊤) (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator F X Y-1∈F.space 1 :=
  product_sub_one_mem F
    (inverse_sub_one_mem F hF (normalizedSolution_sub_one_mem F hY hX _)
      (rightSolution_isUnit F hX hY _))
    (normalizedSolution_sub_one_mem F hX hY _)

end KZCollar

section
namespace FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

 theorem term_above_cutoff (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {n : ℕ} (hn : F.cutoff<n) (a t : ℝ) : term Ω a n t=0 := by
  have h := F.antitone hn (term_mem F hΩ a n t)
  simpa only [F.terminal,Submodule.mem_bot] using h

 theorem stabilize (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {N : ℕ} (hn : F.cutoff ≤ N) (a t : ℝ) :
    transport Ω a N t=transport Ω a F.cutoff t := by
  unfold transport
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro n hnN hnc
  rw [Finset.mem_range,not_lt] at hnc
  exact term_above_cutoff F hΩ (by omega) a t

 def extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N) : NilpotentFiltration A where
  space := F.space
  antitone := F.antitone
  one_mem := F.one_mem
  mul_mem := F.mul_mem
  cutoff := N
  terminal := le_antisymm (le_trans (F.antitone (Nat.add_le_add_right hN 1)) F.terminal.le) bot_le

end FinitePicard
namespace KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]

 omit [CompleteSpace A] in
 theorem normalized_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) (s : ℝ) :
    normalizedSolution (extend F N hN) X Y s=normalizedSolution F X Y s := by
  simp only [normalizedSolution,extend]
  rw [stabilize F (regularForm_mem F hX hY) hN]

 omit [CompleteSpace A] in
 theorem associator_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator (extend F N hN) X Y=associator F X Y := by
  simp only [associator,rightSolution,normalized_extend F N hN hX hY,
    normalized_extend F N hN hY hX]

 variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [FiniteDimensional ℝ B] [CompleteSpace B]

 omit [CompleteSpace A] in
 theorem map_normalized_general (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1)
    (hfX : f X∈G.space 1) (hfY : f Y∈G.space 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s<1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  let N := max F.cutoff G.cutoff
  rw [←normalized_extend F N (le_max_left _ _) hX hY,
    ←normalized_extend G N (le_max_right _ _) hfX hfY]
  exact map_normalizedSolution f (extend F N (le_max_left _ _))
    (extend G N (le_max_right _ _)) rfl hX Y hs hs1

 theorem map_associator_general (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1)
    (hfX : f X∈G.space 1) (hfY : f Y∈G.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  let N := max F.cutoff G.cutoff
  rw [←associator_extend F N (le_max_left _ _) hX hY,
    ←associator_extend G N (le_max_right _ _) hfX hfY]
  exact map_associator f (extend F N (le_max_left _ _))
    (extend G N (le_max_right _ _)) rfl hX hY

end KZCollar

end

namespace CutoffDiagonal
open scoped TensorProduct
open CutoffDepth CutoffKZ FinitePicard
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def left (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N := Algebra.TensorProduct.includeLeft
def right (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N := Algebra.TensorProduct.includeRight
 theorem commute (N : ℕ) (a b : Q ℝ N) : Commute (left N a) (right N b) := by
  change (a⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]b)=((1:Q ℝ N)⊗ₜ[ℝ]b)*(a⊗ₜ[ℝ](1:Q ℝ N))
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
def tensorWeight (N : ℕ) : NilpotentFiltration (Q ℝ N⊗[ℝ]Q ℝ N) :=
  TensorFiltration.cutoff (weight N) (weight N)
 theorem left_mem (N n : ℕ) (u : Q ℝ N) (hu : u∈(weight N).space n) : left N u∈(tensorWeight N).space n :=
  TensorFiltration.tmul_mem _ _ (by omega) hu (weight N).one_mem
 theorem right_mem (N n : ℕ) (u : Q ℝ N) (hu : u∈(weight N).space n) : right N u∈(tensorWeight N).space n :=
  TensorFiltration.tmul_mem _ _ (by omega) (weight N).one_mem hu
def diagonal (N : ℕ) : Q ℝ (N+N) →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N :=
  NilpotentFreeLift.eval (tensorWeight N) (fun b => left N (gen N b)+right N (gen N b))
    (fun b => ((tensorWeight N).space 1).add_mem (left_mem N 1 _ (gen_weight N b)) (right_mem N 1 _ (gen_weight N b)))
 @[simp] theorem diagonal_gen (N : ℕ) (b : Bool) : diagonal N (gen (N+N) b)=left N (gen N b)+right N (gen N b) :=
  NilpotentFreeLift.eval_gen _ _ _ b
 theorem diagonal_mem (N n : ℕ) (u : Q ℝ (N+N)) (hu : u∈(weight (N+N)).space n) :
    diagonal N u∈(tensorWeight N).space n := NilpotentFreeLift.eval_preserves _ _ _ hu

def drop (M N : ℕ) (h : N ≤ M) : Q ℝ M →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (extend (weight N) M h) (gen N) (gen_weight N)
 @[simp] theorem drop_gen (M N : ℕ) (h : N ≤ M) (b : Bool) : drop M N h (gen M b)=gen N b :=
  NilpotentFreeLift.eval_gen _ _ _ b
 theorem drop_mem (M N : ℕ) (h : N ≤ M) (n : ℕ) (u : Q ℝ M) (hu : u∈(weight M).space n) :
    drop M N h u∈(weight N).space n :=
  NilpotentFreeLift.eval_preserves (extend (weight N) M h) (gen N) (gen_weight N) hu
 theorem drop_associator (M N : ℕ) (h : N ≤ M) :
    drop M N h (KZCollar.associator (weight M) (X M) (Y M))=KZCollar.associator (weight N) (X N) (Y N) := by
  rw [KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    (gen_weight M false) (gen_weight M true)
    (drop_mem M N h 1 _ (gen_weight M false)) (drop_mem M N h 1 _ (gen_weight M true)),
    drop_gen,drop_gen]
end CutoffDiagonal

namespace RegularSingular
open MeasureTheory Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def regular (X : A) (R : ℝ → A) (s : ℝ) : A := gauge (-X) s*R s*gauge X s

theorem regular_finite (X : A) (R : ℝ → A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    regular X R s=∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j) := by
  have hnX : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  unfold regular
  rw [gauge_finite (-X) hnX,gauge_finite X hX,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  have hp : (-1:A)^i*X^i*R s*X^j=(-1:ℝ)^i • (X^i*R s*X^j) := by
    simp only [Algebra.smul_def,map_pow,map_neg,map_one]
    noncomm_ring
  rw [hp,smul_smul]
  congr 1
  rw [pow_add]
  ring

theorem regular_integrable (X : A) {R : ℝ → A} {N : ℕ} (hX : X^(N+1)=0)
    {b : ℝ} (hb : 0≤b) (hR : ContinuousOn R (Icc 0 b)) :
    IntervalIntegrable (regular X R) volume 0 b := by
  have h : regular X R=fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j) :=
    funext (regular_finite X R hX)
  rw [h]
  have hi (i j : ℕ) : IntervalIntegrable (fun s =>
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) volume 0 b :=
    ((LogCollar.log_pow (i+j) hb).mul_const _).smul_continuousOn
      (by rw [uIcc_of_le hb]; exact (continuousOn_const.mul hR).mul continuousOn_const)
  have hh := IntervalIntegrable.sum (ε:=A) (Finset.range (N+1))
    (fun i _ => IntervalIntegrable.sum (ε:=A) (Finset.range (N+1)) (fun j _ => hi i j))
  have he : (∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1), fun s =>
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) =
      (fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) := by
    ext s
    simp only [Finset.sum_apply]
  rw [he] at hh
  exact hh

theorem regular_mem (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hR : ∀ s,R s∈F.space 1) (s : ℝ) : regular X R s∈F.space 1 := by
  rw [regular_finite X R (pow_cutoff_eq_zero F hX)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact F.antitone (by omega : 1 ≤ i+1+j)
    (F.mul_mem (i+1) j (F.mul_mem i 1 (pow_mem F hX i) (hR s)) (pow_mem F hX j))

def solution (F : NilpotentFiltration A) (X : A) (R : ℝ → A) (s : ℝ) : A :=
  gauge X s*transport (regular X R) 0 F.cutoff s

variable [CompleteSpace A]

theorem regular_continuous {X : A} {R : ℝ → A} {b : ℝ}
    (hR : ContinuousOn R (Icc 0 b)) : ContinuousOn (regular X R) (Ioo 0 b) := by
  intro s hs
  have hg (X : A) : ContinuousAt (gauge X) s := (gauge_derivative X (ne_of_gt hs.1)).continuousAt
  exact (((hg (-X)).continuousWithinAt.mul ((hR.mono Ioo_subset_Icc_self) s hs)).mul
    (hg X).continuousWithinAt)

omit [CompleteSpace A] in
theorem solution_limit (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} {b : ℝ} (hb : 0<b) (hR : ContinuousOn R (Icc 0 b)) [CompleteSpace A] :
    Tendsto (fun s => gauge (-X) s*solution F X R s) (𝓝[>] 0) (𝓝 (1:A)) := by
  have he : (fun s => gauge (-X) s*solution F X R s)=transport (regular X R) 0 F.cutoff := by
    funext s
    rw [solution,←mul_assoc,gauge_neg_mul,one_mul]
  rw [he]
  have h := collar_limit (regular_integrable X (pow_cutoff_eq_zero F hX) hb.le hR) F.cutoff
  rw [uIcc_of_le hb.le,nhdsWithin_Icc_eq_nhdsGE hb] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

variable [FiniteDimensional ℝ A]

theorem solution_derivative (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hRm : ∀ s,R s∈F.space 1) {b s : ℝ}
    (hR : ContinuousOn R (Icc 0 b)) (hs : s∈Ioo 0 b) :
    HasDerivAt (solution F X R) ((s⁻¹ • X+R s)*solution F X R s) s := by
  have hi := regular_integrable X (pow_cutoff_eq_zero F hX) (hs.1.le.trans hs.2.le) hR
  have hh := derivative_nilpotent_transport F (regular_mem F hX hRm) hi (regular_continuous hR) hs
  apply ((gauge_derivative X (ne_of_gt hs.1)).mul hh).congr_deriv
  let P := transport (regular X R) 0 F.cutoff s
  change (s⁻¹ • (X*gauge X s))*P+gauge X s*((gauge (-X) s*R s*gauge X s)*P)=
    (s⁻¹ • X+R s)*(gauge X s*P)
  rw [←mul_assoc (gauge X s),←mul_assoc (gauge X s),←mul_assoc (gauge X s),gauge_mul_neg,one_mul]
  simp only [add_mul,smul_mul_assoc,mul_assoc]

theorem solution_isUnit (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hR : ∀ s,R s∈F.space 1) (s : ℝ) : IsUnit (solution F X R s) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (NormedSpace.isUnit_exp _).mul (transport_isUnit F (regular_mem F hX hR) 0 s F.cutoff)

end RegularSingular

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def integralNorm (Ω : ℝ → A) (a b : ℝ) : ℝ := ∫ s in a..b,‖Ω s‖

omit [NormedAlgebra ℝ A] in
theorem integralNorm_nonneg (Ω : ℝ → A) {a b : ℝ} (hab : a≤b) :
    0 ≤ integralNorm Ω a b := integral_nonneg hab (fun _ _ => norm_nonneg _)

theorem norm_term_le {Ω : ℝ → A} {a b L : ℝ} (hab : a≤b)
    (hi : IntervalIntegrable Ω volume a b) (hL : 0≤L)
    (hbound : ∀ t∈Icc a b,integralNorm Ω a t≤L) (n : ℕ) :
    ∀ t∈Icc a b,‖term Ω a n t‖≤‖(1:A)‖*L^n := by
  induction n with
  | zero => intro t ht; simp only [term_zero,pow_zero,mul_one,le_refl]
  | succ n ih =>
    intro t ht
    have his : IntervalIntegrable Ω volume a t := hi.mono_set (by simpa only [uIcc_of_le hab,uIcc_of_le ht.1] using Icc_subset_Icc_right ht.2)
    have hcont := continuousOn_term hi n
    have hm : IntervalIntegrable (fun s => Ω s*term Ω a n s) volume a t :=
      (hi.mul_continuousOn hcont).mono_set (by simpa only [uIcc_of_le hab,uIcc_of_le ht.1] using Icc_subset_Icc_right ht.2)
    calc
      ‖term Ω a (n+1) t‖ ≤ ∫ s in a..t,‖Ω s*term Ω a n s‖ := norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t,‖Ω s‖*(‖(1:A)‖*L^n) := by
        apply integral_mono_on ht.1 hm.norm (his.norm.mul_const _)
        intro s hs
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih s ⟨hs.1,hs.2.trans ht.2⟩) (norm_nonneg _))
      _ = integralNorm Ω a t*(‖(1:A)‖*L^n) := integral_mul_const _ _
      _ ≤ L*(‖(1:A)‖*L^n) := mul_le_mul_of_nonneg_right (hbound t ht) (mul_nonneg (norm_nonneg _) (pow_nonneg hL _))
      _ = ‖(1:A)‖*L^(n+1) := by rw [pow_succ]; ring

omit [NormedAlgebra ℝ A] in
theorem integrable_partial {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (ht : t∈Icc a b) :
    IntervalIntegrable Ω volume a t :=
  hi.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)]
    using Icc_subset_Icc_right ht.2)

omit [NormedAlgebra ℝ A] in
theorem integralNorm_partial {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (ht : t∈Icc a b) :
    integralNorm Ω a t≤ integralNorm Ω a b :=
  integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall (fun s => norm_nonneg (Ω s))) hi.norm

theorem norm_term_bound {Ω : ℝ → A} {a b : ℝ} (hi : IntervalIntegrable Ω volume a b)
    (n : ℕ) {t : ℝ} (ht : t∈Icc a b) :
    ‖term Ω a n t‖≤‖(1:A)‖*(integralNorm Ω a b)^n :=
  norm_term_le (ht.1.trans ht.2) hi (integralNorm_nonneg Ω (ht.1.trans ht.2))
    (fun _ hs => integralNorm_partial hi hs) n t ht

theorem norm_term_sub_le {Ω Θ : ℝ → A} {a b L E : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hΘ : IntervalIntegrable Θ volume a b)
    (hL : 0≤L) (hE : 0≤E)
    (hΩL : integralNorm Ω a b≤L) (hΘL : integralNorm Θ a b≤L)
    (hEL : integralNorm (fun s => Ω s-Θ s) a b≤E) (n : ℕ) :
    ∀ t∈Icc a b,‖term Ω a n t-term Θ a n t‖≤(‖(1:A)‖*E)*(n:ℝ)*(L+1)^n := by
  have hM : 0≤L+1 := by positivity
  have hML : L≤L+1 := by linarith
  have cΩ := norm_term_le hab hΩ hM (fun t ht => (integralNorm_partial hΩ ht).trans (hΩL.trans hML))
  induction n with
  | zero => intro t ht; simp
  | succ n ih =>
    intro t ht
    have hiΩ := integrable_partial (hΩ.mul_continuousOn (continuousOn_term hΩ n)) ht
    have hiΘ := integrable_partial (hΘ.mul_continuousOn (continuousOn_term hΘ n)) ht
    have hsΩ := integrable_partial hΩ ht
    have hsΘ := integrable_partial hΘ ht
    have hd := integralNorm_partial (hΩ.sub hΘ) ht
    have hbΘ := (integralNorm_partial hΘ ht).trans hΘL
    have hp : 0≤(L+1)^n := pow_nonneg hM n
    have hC : 0≤‖(1:A)‖ := norm_nonneg _
    calc
      ‖term Ω a (n+1) t-term Θ a (n+1) t‖ =
        ‖∫ s in a..t,Ω s*term Ω a n s-Θ s*term Θ a n s‖ := by rw [integral_sub hiΩ hiΘ]; rfl
      _ ≤ ∫ s in a..t,‖Ω s*term Ω a n s-Θ s*term Θ a n s‖ := norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t,‖Ω s-Θ s‖*(‖(1:A)‖*(L+1)^n)+‖Θ s‖*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) := by
        apply integral_mono_on ht.1 (hiΩ.sub hiΘ).norm
          (((hsΩ.sub hsΘ).norm.mul_const _).add (hsΘ.norm.mul_const _))
        intro s hs
        have hs' : s∈Icc a b := ⟨hs.1,hs.2.trans ht.2⟩
        calc
          _ = ‖(Ω s-Θ s)*term Ω a n s+Θ s*(term Ω a n s-term Θ a n s)‖ := by congr 1; noncomm_ring
          _ ≤ ‖(Ω s-Θ s)*term Ω a n s‖+‖Θ s*(term Ω a n s-term Θ a n s)‖ := norm_add_le _ _
          _ ≤ ‖Ω s-Θ s‖*‖term Ω a n s‖+‖Θ s‖*‖term Ω a n s-term Θ a n s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_left (cΩ n s hs') (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (ih s hs') (norm_nonneg _))
      _ = integralNorm (fun s => Ω s-Θ s) a t*(‖(1:A)‖*(L+1)^n)+
          integralNorm Θ a t*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) := by
        rw [integral_add ((hsΩ.sub hsΘ).norm.mul_const _) (hsΘ.norm.mul_const _),intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const]; rfl
      _ ≤ E*(‖(1:A)‖*(L+1)^n)+L*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) :=
        add_le_add (mul_le_mul_of_nonneg_right (hd.trans hEL) (mul_nonneg hC hp))
          (mul_le_mul_of_nonneg_right hbΘ (by positivity))
      _ = (‖(1:A)‖*E*(L+1)^n)*(1+L*(n:ℝ)) := by ring
      _ ≤ (‖(1:A)‖*E*(L+1)^n)*(((n:ℝ)+1)*(L+1)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
        nlinarith
      _ = (‖(1:A)‖*E)*((n+1:ℕ):ℝ)*(L+1)^(n+1) := by rw [Nat.cast_add,Nat.cast_one,pow_succ]; ring

def transportPoly (N : ℕ) (u : ℝ) : ℝ := ∑ n∈Finset.range (N+1),u^n

def errorPoly (N : ℕ) (u : ℝ) : ℝ := ∑ n∈Finset.range (N+1),(n:ℝ)*u^n

theorem norm_transport_le {Ω : ℝ → A} {a b L : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hL : 0≤L)
    (hb : integralNorm Ω a b≤L) (N : ℕ) :
    ‖transport Ω a N b‖≤‖(1:A)‖*transportPoly N L := by
  calc
    _ ≤ ∑ n∈Finset.range (N+1),‖term Ω a n b‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range (N+1),‖(1:A)‖*L^n :=
      Finset.sum_le_sum (fun n _ => norm_term_le hab hΩ hL
        (fun _ ht => (integralNorm_partial hΩ ht).trans hb) n b ⟨hab,le_rfl⟩)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem norm_transport_sub_le {Ω Θ : ℝ → A} {a b L E : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hΘ : IntervalIntegrable Θ volume a b)
    (hL : 0≤L) (hE : 0≤E)
    (hΩL : integralNorm Ω a b≤L) (hΘL : integralNorm Θ a b≤L)
    (hEL : integralNorm (fun s => Ω s-Θ s) a b≤E) (N : ℕ) :
    ‖transport Ω a N b-transport Θ a N b‖≤(‖(1:A)‖*E)*errorPoly N (L+1) := by
  unfold transport
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n∈Finset.range (N+1),‖term Ω a n b-term Θ a n b‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range (N+1),(‖(1:A)‖*E)*(n:ℝ)*(L+1)^n :=
      Finset.sum_le_sum (fun n _ => norm_term_sub_le hab hΩ hΘ hL hE hΩL hΘL hEL n b ⟨hab,le_rfl⟩)
    _ = _ := by simp only [errorPoly,Finset.mul_sum,mul_assoc]

end FinitePicard

namespace PowerAsymptotic

section
open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology

def Subpower {E : Type*} [Norm E] (f : ℝ → E) : Prop :=
  ∀ p : ℝ,0<p → f =O[𝓝[>] 0] (fun s : ℝ => s^(-p))

def PowerSmall {E : Type*} [Norm E] (f : ℝ → E) : Prop :=
  ∃ p : ℝ,0<p ∧ f =O[𝓝[>] 0] (fun s : ℝ => s^p)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma rpow_mul_eventually (p q : ℝ) :
    (fun s : ℝ => s^p*s^q) =ᶠ[𝓝[>] 0] (fun s : ℝ => s^(p+q)) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (Real.rpow_add (show 0<s from hs) p q).symm

theorem log_pow_subpower (n : ℕ) : Subpower (fun s : ℝ => Real.log s^n) := by
  intro p hp
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n:ℝ) (neg_lt_zero.mpr hp)).isBigO
  apply IsBigO.of_norm_left
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,norm_pow] using h

omit [NormedAlgebra ℝ A] in
theorem Subpower.add {f g : ℝ → A} (hf : Subpower f) (hg : Subpower g) :
    Subpower (fun s => f s+g s) := fun p hp => (hf p hp).add (hg p hp)

omit [NormedAlgebra ℝ A] in
theorem Subpower.mul {f g : ℝ → A} (hf : Subpower f) (hg : Subpower g) :
    Subpower (fun s => f s*g s) := by
  intro p hp
  have h := (hf (p/2) (by linarith)).mul (hg (p/2) (by linarith))
  apply h.congr' .rfl
  filter_upwards [rpow_mul_eventually (-(p/2)) (-(p/2))] with s hs
  convert! hs using 1
  congr 1
  ring

theorem const_subpower (a : A) : Subpower (fun _ : ℝ => a) := by
  intro p hp
  have h := (log_pow_subpower 0 p hp)
  have h' := h.smul (isBigO_const_const a (one_ne_zero : (1:ℝ)≠0) (𝓝[>] (0:ℝ)))
  simpa only [pow_zero,one_smul,smul_eq_mul,mul_one] using h'

omit [NormedAlgebra ℝ A] in
theorem continuousAt_subpower {f : ℝ → A} (hf : ContinuousAt f 0) : Subpower f := by
  intro p hp
  exact (isBigO_const_of_tendsto hf (one_ne_zero : (1:ℝ)≠0)).mono inf_le_left |>.trans
    (by simpa only [pow_zero] using! log_pow_subpower 0 p hp)

theorem gauge_subpower {X : A} {N : ℕ} (hX : X^(N+1)=0) : Subpower (gauge X) := by
  intro p hp
  have h (i : ℕ) : (fun s : ℝ => (Real.log s^i / (i.factorial:ℝ)) • X^i)
      =O[𝓝[>] 0] (fun s : ℝ => s^(-p)) := by
    have hr := (log_pow_subpower i p hp).smul
      (isBigO_const_const (((i.factorial:ℝ)⁻¹) • X^i) (one_ne_zero : (1:ℝ)≠0) (𝓝[>] (0:ℝ)))
    simpa only [smul_smul,smul_eq_mul,mul_one,div_eq_mul_inv] using hr
  have hh := IsBigO.sum (s:=Finset.range (N+1)) (fun i _ => h i)
  apply hh.congr_left
  intro s
  simp only [Finset.sum_apply]
  exact (gauge_finite X hX s).symm

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.mul_subpower {f g : ℝ → A} (hf : PowerSmall f) (hg : Subpower g) :
    PowerSmall (fun s => f s*g s) := by
  obtain ⟨p,hp,hf⟩ := hf
  refine ⟨p/2,by linarith,?_⟩
  apply (hf.mul (hg (p/2) (by linarith))).congr' .rfl
  filter_upwards [rpow_mul_eventually p (-(p/2))] with s hs
  convert! hs using 1
  congr 1
  ring

omit [NormedAlgebra ℝ A] in
omit [NormedAlgebra ℝ A] in
theorem Subpower.mul_powerSmall {f g : ℝ → A} (hf : Subpower f) (hg : PowerSmall g) :
    PowerSmall (fun s => f s*g s) := by
  obtain ⟨p,hp,hg⟩ := hg
  refine ⟨p/2,by linarith,?_⟩
  apply ((hf (p/2) (by linarith)).mul hg).congr' .rfl
  filter_upwards [rpow_mul_eventually (-(p/2)) p] with s hs
  convert! hs using 1
  congr 1
  ring

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.tendsto_zero {f : ℝ → A} (hf : PowerSmall f) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨p,hp,hf⟩ := hf
  apply hf.trans_tendsto
  simpa only [Real.zero_rpow (ne_of_gt hp)] using!
    (Real.continuousAt_rpow_const (x:=(0:ℝ)) p (Or.inr hp.le)).tendsto.mono_left inf_le_left

omit [NormedAlgebra ℝ A] in

theorem integralNorm_isBigO {Ω : ℝ → A} {b r : ℝ} (hb : 0<b) (hr : -1<r)
    (hi : IntervalIntegrable Ω volume 0 b)
    (ho : Ω =O[𝓝[>] 0] (fun s : ℝ => s^r)) :
    (fun s => integralNorm Ω 0 s) =O[𝓝[>] 0] (fun s : ℝ => s^(r+1)) := by
  obtain ⟨C,hC,hbound⟩ := ho.exists_nonneg
  obtain ⟨c,hc,hcb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hbound.bound
  let d := min b c
  have hd : 0<d := lt_min hb hc
  apply isBigO_iff.mpr
  refine ⟨C/(r+1),?_⟩
  filter_upwards [Ioc_mem_nhdsGT hd] with s hs
  have hs0 : 0 ≤ s := hs.1.le
  have hsb : s ≤ b := hs.2.trans (min_le_left _ _)
  have his := integrable_partial hi ⟨hs0,hsb⟩
  have hir : IntervalIntegrable (fun t : ℝ => C*t^r) volume 0 s :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul C
  have hbnd : integralNorm Ω 0 s ≤ C/(r+1)*s^(r+1) := by
    calc
      _ ≤ ∫ t in 0..s,C*t^r := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs0 his.norm hir
        intro t ht
        have ht0 : 0<t := ht.1
        have hh := hcb (show t∈Ioc 0 c from ⟨ht0,ht.2.le.trans (hs.2.trans (min_le_right _ _))⟩)
        simpa only [Set.mem_ofPred_eq,Real.norm_of_nonneg (Real.rpow_nonneg ht0.le r)] using hh
      _ = C/(r+1)*s^(r+1) := by
        rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hr),
          Real.zero_rpow (by linarith : r+1≠0),sub_zero]
        ring
  simpa only [Real.norm_of_nonneg (integralNorm_nonneg Ω hs0),
    Real.norm_of_nonneg (Real.rpow_nonneg hs0 (r+1))] using hbnd

theorem transport_sub_one_isBigO_integralNorm {Ω : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hi : IntervalIntegrable Ω volume 0 b) (N : ℕ) :
    (fun s => transport Ω 0 N s-1) =O[𝓝[>] 0] (fun s => integralNorm Ω 0 s) := by
  let L := integralNorm Ω 0 b
  let C := ∑ n∈Finset.range N,‖(1:A)‖*L^n
  apply isBigO_iff.mpr
  refine ⟨C,?_⟩
  filter_upwards [Ioc_mem_nhdsGT hb] with s hs
  have hs' : s∈Icc 0 b := ⟨hs.1.le,hs.2⟩
  have his := integrable_partial hi hs'
  have hn (n : ℕ) : ‖term Ω 0 (n+1) s‖ ≤ integralNorm Ω 0 s*(‖(1:A)‖*L^n) := by
    have hit := integrable_partial (hi.mul_continuousOn (continuousOn_term hi n)) hs'
    calc
      _ ≤ ∫ t in 0..s,‖Ω t*term Ω 0 n t‖ := intervalIntegral.norm_integral_le_integral_norm hs.1.le
      _ ≤ ∫ t in 0..s,‖Ω t‖*(‖(1:A)‖*L^n) := by
        apply intervalIntegral.integral_mono_on hs.1.le hit.norm (his.norm.mul_const _)
        intro t ht
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (norm_term_bound hi n ⟨ht.1,ht.2.trans hs.2⟩) (norm_nonneg _))
      _ = _ := intervalIntegral.integral_mul_const _ _
  have he : transport Ω 0 N s-1=∑ n∈Finset.range N,term Ω 0 (n+1) s := by
    simp only [transport,Finset.sum_range_succ',term_zero,add_sub_cancel_right]
  rw [he,Real.norm_of_nonneg (integralNorm_nonneg Ω hs.1.le)]
  calc
    _ ≤ ∑ n∈Finset.range N,‖term Ω 0 (n+1) s‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range N,integralNorm Ω 0 s*(‖(1:A)‖*L^n) :=
      Finset.sum_le_sum (fun n _ => hn n)
    _ = C*integralNorm Ω 0 s := by rw [←Finset.mul_sum]; exact mul_comm _ _

theorem transport_sub_one_powerSmall {Ω : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hi : IntervalIntegrable Ω volume 0 b) (ho : Subpower Ω) (N : ℕ) :
    PowerSmall (fun s => transport Ω 0 N s-1) := by
  refine ⟨1/2,by norm_num,?_⟩
  have h := (transport_sub_one_isBigO_integralNorm hb hi N).trans
    (integralNorm_isBigO hb (by norm_num : -1 < -(1/2:ℝ)) hi (ho (1/2) (by norm_num)))
  convert! h using 1
  norm_num

end

open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem tendsto_subpower {f : ℝ → A} {a : A} (hf : Tendsto f (𝓝[>] 0) (𝓝 a)) : Subpower f := by
  intro p hp
  exact (isBigO_const_of_tendsto hf (one_ne_zero : (1:ℝ)≠0)).trans
    (by simpa only [pow_zero] using! log_pow_subpower 0 p hp)

omit [NormedAlgebra ℝ A] in
theorem continuousOn_subpower {R : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hR : ContinuousOn R (Icc 0 b)) : Subpower R := by
  have h := hR 0 (left_mem_Icc.mpr hb.le)
  rw [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE hb] at h
  exact tendsto_subpower (h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.of_isBigO {f g : ℝ → A} (hg : PowerSmall g) (hfg : f =O[𝓝[>] 0] g) :
    PowerSmall f := by
  obtain ⟨p,hp,hg⟩ := hg
  exact ⟨p,hp,hfg.trans hg⟩

omit [NormedAlgebra ℝ A] in
theorem Subpower.of_isBigO {f g : ℝ → A} (hg : Subpower g) (hfg : f =O[𝓝[>] 0] g) :
    Subpower f := fun p hp => hfg.trans (hg p hp)

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.congr {f g : ℝ → A} (hf : PowerSmall f) (hh : ∀ s,f s=g s) :
    PowerSmall g := by
  obtain ⟨p,hp,hf⟩ := hf
  exact ⟨p,hp,hf.congr_left hh⟩

theorem regular_subpower {X : A} {N : ℕ} (hX : X^(N+1)=0)
    {R : ℝ → A} (hR : Subpower R) : Subpower (regular X R) :=
  ((gauge_subpower (by rw [neg_pow,hX,mul_zero] : (-X)^(N+1)=0)).mul hR).mul (gauge_subpower hX)

theorem solution_sub_gauge {X : A} (F : NilpotentFiltration A) (hX : X∈F.space 1)
    {R : ℝ → A} {b : ℝ} (hb : 0 < b) (hR : ContinuousOn R (Icc 0 b)) :
    PowerSmall (fun s => solution F X R s-gauge X s) := by
  have h := transport_sub_one_powerSmall hb (regular_integrable X (pow_cutoff_eq_zero F hX) hb.le hR)
    (regular_subpower (pow_cutoff_eq_zero F hX) (continuousOn_subpower hb hR)) F.cutoff
  apply ((gauge_subpower (pow_cutoff_eq_zero F hX)).mul_powerSmall h).congr
  intro s
  simp only [solution,mul_sub,mul_one]

theorem Subpower.pow {f : ℝ → A} (hf : Subpower f) (n : ℕ) : Subpower (fun s => f s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const_subpower (1:A)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

omit [NormedAlgebra ℝ A] in
theorem Subpower.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → A}
    (hf : ∀ i∈S,Subpower (f i)) : Subpower (fun s => ∑ i∈S,f i s) := by
  intro p hp
  have h := IsBigO.sum (fun i hi => hf i hi p hp)
  apply h.congr_left
  intro s
  simp only [Finset.sum_apply]

theorem errorPoly_subpower {L : ℝ → ℝ} (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => errorPoly N (L s+1)) := by
  apply Subpower.sum
  intro n hn
  exact (const_subpower (n:ℝ)).mul ((hL.add (const_subpower 1)).pow n)

variable [CompleteSpace A]

omit [NormedAlgebra ℝ A] in
theorem inverse_tendsto_one {f : ℝ → A} (hf : Tendsto f (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun s => Ring.inverse (f s)) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Units.val_one,Ring.inverse_one] using! (NormedRing.inverse_continuousAt (1:Aˣ)).tendsto.comp hf

omit [NormedAlgebra ℝ A] in
theorem inverse_sub_one_powerSmall {f : ℝ → A} (hu : ∀ s,IsUnit (f s))
    (hf : PowerSmall (fun s => f s-1)) : PowerSmall (fun s => Ring.inverse (f s)-1) := by
  have ht : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add,sub_add_cancel] using! hf.tendsto_zero.add_const (1:A)
  have hi := tendsto_subpower (inverse_tendsto_one ht)
  have h := hi.mul_powerSmall hf
  obtain ⟨p,hp,h⟩ := h
  refine ⟨p,hp,?_⟩
  apply h.neg_left.congr_left
  intro s
  rw [mul_sub,mul_one,Ring.inverse_mul_cancel _ (hu s),neg_sub]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem inverse_mul_of_units {a b : A} (ha : IsUnit a) (hb : IsUnit b) :
    Ring.inverse (a*b)=Ring.inverse b*Ring.inverse a := by
  obtain ⟨u,rfl⟩ := ha
  obtain ⟨v,rfl⟩ := hb
  rw [←Units.val_mul,Ring.inverse_unit,Ring.inverse_unit,Ring.inverse_unit,mul_inv_rev]
  rfl

theorem inverse_gauge (X : A) (s : ℝ) : Ring.inverse (gauge X s)=gauge (-X) s := by
  have hu : IsUnit (gauge X s) := by
    let := NormedAlgebra.restrictScalars ℚ ℝ A
    exact NormedSpace.isUnit_exp _
  calc
    _ = Ring.inverse (gauge X s)*(gauge X s*gauge (-X) s) := by rw [gauge_mul_neg,mul_one]
    _ = gauge (-X) s := by rw [←mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]

variable [FiniteDimensional ℝ A]

theorem inverse_solution_sub_gauge {X : A} (F : NilpotentFiltration A) (hX : X∈F.space 1)
    {R : ℝ → A} (hRm : ∀ s,R s∈F.space 1) {b : ℝ} (hb : 0 < b)
    (hR : ContinuousOn R (Icc 0 b)) :
    PowerSmall (fun s => Ring.inverse (solution F X R s)-gauge (-X) s) := by
  have hnil := pow_cutoff_eq_zero F hX
  have hh := transport_sub_one_powerSmall hb (regular_integrable X hnil hb.le hR)
    (regular_subpower hnil (continuousOn_subpower hb hR)) F.cutoff
  have hu (s : ℝ) := transport_isUnit F (regular_mem F hX hRm) 0 s F.cutoff
  have hi := inverse_sub_one_powerSmall hu hh
  apply (hi.mul_subpower (gauge_subpower (by rw [neg_pow,hnil,mul_zero] : (-X)^(F.cutoff+1)=0))).congr
  intro s
  have hg : IsUnit (gauge X s) := by
    let := NormedAlgebra.restrictScalars ℚ ℝ A
    exact NormedSpace.isUnit_exp _
  rw [solution,inverse_mul_of_units hg (hu s),inverse_gauge,sub_mul,one_mul]

end PowerAsymptotic

namespace KZCollar
open Set Filter PowerAsymptotic Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem subpower_congrEventual {f g : ℝ → A} (hf : Subpower f) (hfg : f =ᶠ[𝓝[>] 0] g) :
    Subpower g := fun p hp => (hf p hp).congr' hfg .rfl

theorem linear_powerSmall (c : ℝ) : PowerSmall (fun s : ℝ => c*s) := by
  refine ⟨1,by norm_num,IsBigO.of_bound |c| ?_⟩
  filter_upwards [] with s
  simp only [Real.rpow_one,Real.norm_eq_abs,abs_mul,le_refl]

theorem gauge_at_larger_subpower {X : A} {N : ℕ} (hX : X^(N+1)=0) {r : ℝ → ℝ}
    (hr : Tendsto r (𝓝[>] 0) (𝓝[>] 0)) (hle : ∀ᶠ s in 𝓝[>] 0,s ≤ r s) :
    Subpower (fun s => gauge X (r s)) := by
  intro p hp
  have h := (gauge_subpower hX p hp).comp_tendsto hr
  apply h.trans
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [self_mem_nhdsWithin,hle] with s hs hsr
  change ‖(r s)^(-p)‖ ≤ s^(-p)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hs.le.trans hsr) _)]
  exact Real.rpow_le_rpow_of_nonpos hs hsr (by linarith)

variable [CompleteSpace A]

theorem gauge_mul_scale (X : A) {r s : ℝ} (hr : r≠0) (hs : s≠0) :
    gauge X (r*s)=gauge X r*gauge X s := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [Real.log_mul hr hs,add_smul,NormedSpace.exp_add_of_commute]
  exact (Commute.refl X).smul_left _ |>.smul_right _

theorem gauge_add_of_commute {X Y : A} (h : Commute X Y) (s : ℝ) :
    gauge (X+Y) s=gauge X s*gauge Y s := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_add,NormedSpace.exp_add_of_commute ((h.smul_left _).smul_right _)]

theorem gauge_continuousAt {X : A} {s : ℝ} (hs : s≠0) : ContinuousAt (gauge X) s :=
  (gauge_derivative X hs).continuousAt

omit [CompleteSpace A] in
@[simp] theorem gauge_one (X : A) : gauge X 1=1 := by simp [gauge]

theorem gauge_ratio_limit (X : A) :
    Tendsto (fun s : ℝ => gauge X (1+s)) (𝓝[>] 0) (𝓝 (1:A)) := by
  have ht : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using! (tendsto_const_nhds (x:=(1:ℝ))).add
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))
  simpa only [gauge_one] using! (gauge_continuousAt (X:=X) (by norm_num : (1:ℝ)≠0)).tendsto.comp ht

end KZCollar

namespace FinitePicard

section
open MeasureTheory Set KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def centralizer (Z : A) : Submodule ℝ A where
  carrier := {a | Commute Z a}
  zero_mem' := Commute.zero_right Z
  add_mem' := fun h h' => h.add_right h'
  smul_mem' := fun r _ h => h.smul_right r

variable [FiniteDimensional ℝ A]

theorem term_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (n : ℕ) (t : ℝ) :
    Commute Z (term Ω a n t) := by
  induction n generalizing t with
  | zero => exact Commute.one_right Z
  | succ n ih =>
    exact integral_mem_submodule (centralizer Z) (fun s => Ω s*term Ω a n s) a t
      (fun s => (hΩ s).mul_right (ih s))

theorem transport_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (N : ℕ) (t : ℝ) :
    Commute Z (transport Ω a N t) :=
  Commute.sum_right (Finset.range (N+1)) _ Z (fun n _ => term_commute Z hΩ a n t)

omit [FiniteDimensional ℝ A] in
theorem gauge_commute {X Z : A} {N : ℕ} (hX : X^(N+1)=0) (h : Commute Z X) (s : ℝ) :
    Commute Z (gauge X s) := by
  rw [gauge_finite X hX]
  exact Commute.sum_right _ _ Z (fun n _ => (h.pow_right n).smul_right _)

end

open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_add_commute (F : NilpotentFiltration A) {Ω Ξ : ℝ → A}
    (hΩ : ∀ s,Ω s∈F.space 1) (hΞ : ∀ s,Ξ s∈F.space 1)
    {a b : ℝ} (hab : a<b) (hiΩ : IntervalIntegrable Ω volume a b)
    (hiΞ : IntervalIntegrable Ξ volume a b)
    (hcΩ : ContinuousOn Ω (Ioo a b)) (hcΞ : ContinuousOn Ξ (Ioo a b))
    (hcomm : ∀ s t,Commute (Ξ s) (Ω t)) :
    transport (fun s => Ω s+Ξ s) a F.cutoff b=
      transport Ω a F.cutoff b*transport Ξ a F.cutoff b := by
  let f := fun t => transport Ω a F.cutoff t*transport Ξ a F.cutoff t
  have hf : ∀ s∈Ioo a b,HasDerivAt f ((Ω s+Ξ s)*f s) s := by
    intro s hs
    apply ((derivative_nilpotent_transport F hΩ hiΩ hcΩ hs).mul
      (derivative_nilpotent_transport F hΞ hiΞ hcΞ hs)).congr_deriv
    dsimp only [f]
    have hh := transport_commute (Ξ s) (hcomm s) a F.cutoff s
    rw [mul_assoc,←mul_assoc (transport Ω a F.cutoff s) (Ξ s),←hh.eq,mul_assoc]
    rw [add_mul]
  have hfc : ContinuousOn f (Icc a b) := by
    have hc₁ := continuousOn_transport hiΩ F.cutoff
    have hc₂ := continuousOn_transport hiΞ F.cutoff
    rw [uIcc_of_le hab.le] at hc₁ hc₂
    exact hc₁.mul hc₂
  have hu : ∀ s∈Icc a b,IsUnit (f s) := fun s _ =>
    (transport_isUnit F hΩ a s F.cutoff).mul (transport_isUnit F hΞ a s F.cutoff)
  rw [transport_eq_fundamental F (fun s => (F.space 1).add_mem (hΩ s) (hΞ s))
    hab (hiΩ.add hiΞ) (hcΩ.add hcΞ) hf hfc hu]
  simp only [f,transport_base,mul_one,Ring.inverse_one]

end FinitePicard

namespace KZProduct
open FinitePicard KZCollar MeasureTheory Set
variable {A B C : Type*} [NormedRing A] [NormedRing B] [NormedRing C]
  [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAlgebra ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] [CompleteSpace C]
variable (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] C) (hc : ∀ a b,Commute (f a) (g b))

include hc
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] in
 theorem shuffle (a c : A) (b d : B) :
    (f a*g b)*(f c*g d)=f (a*c)*g (b*d) := by
  rw [(hc c b).symm.mul_mul_mul_comm,map_mul,map_mul]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] in
 theorem gauge_sum {X : A} {Y : B} {M N : ℕ}
    (hX : X^(M+1)=0) (hY : Y^(N+1)=0) (s : ℝ) :
    gauge (f X+g Y) s=f (gauge X s)*g (gauge Y s) := by
  rw [gauge_add_of_commute (hc X Y),←map_gauge f X hX,←map_gauge g Y hY]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] in
 theorem regular_sum {X Y : A} {Z T : B} {M N : ℕ}
    (hX : X^(M+1)=0) (hZ : Z^(N+1)=0) (s : ℝ) :
    regularForm (f X+g Z) (f Y+g T) s=f (regularForm X Y s)+g (regularForm Z T s) := by
  have hXn : (-X)^(M+1)=0 := by rw [neg_pow,hX,mul_zero]
  have hZn : (-Z)^(N+1)=0 := by rw [neg_pow,hZ,mul_zero]
  have hn : -(f X+g Z)=f (-X)+g (-Z) := by rw [map_neg,map_neg,neg_add]
  simp only [regularForm,hn,gauge_sum f g hc hX hZ,gauge_sum f g hc hXn hZn]
  have hm : (s-1)⁻¹ • (f Y+g T)=f ((s-1)⁻¹ • Y)*g 1+f 1*g ((s-1)⁻¹ • T) := by
    simp only [smul_add,map_smul,map_one,mul_one,one_mul]
  rw [hm,mul_add,add_mul,shuffle f g hc,shuffle f g hc,
    shuffle f g hc,shuffle f g hc]
  simp only [mul_one,one_mul,gauge_neg_mul,map_one]

omit [CompleteSpace A] [CompleteSpace B] in
 theorem normalized_sum (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    (H : NilpotentFiltration C) {X Y : A} {Z T : B}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈G.space 1) (hT : T∈G.space 1)
    (hfX : f X∈H.space 1) (hfY : f Y∈H.space 1)
    (hgZ : g Z∈H.space 1) (hgT : g T∈H.space 1)
    {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    normalizedSolution H (f X+g Z) (f Y+g T) s=
      f (normalizedSolution F X Y s)*g (normalizedSolution G Z T s) := by
  have hfn : (f X)^(F.cutoff+1)=0 := by rw [←map_pow,pow_cutoff_eq_zero F hX,map_zero]
  have hgn : (g Z)^(G.cutoff+1)=0 := by rw [←map_pow,pow_cutoff_eq_zero G hZ,map_zero]
  have hreg (r : ℝ) : regularForm (f X+g Z) (f Y+g T) r=
      regularForm (f X) (f Y) r+regularForm (g Z) (g T) r := by
    rw [regular_sum f g hc (pow_cutoff_eq_zero F hX) (pow_cutoff_eq_zero G hZ),
      map_regularForm f X Y (pow_cutoff_eq_zero F hX),map_regularForm g Z T (pow_cutoff_eq_zero G hZ)]
  have hcomm (r t : ℝ) : Commute (regularForm (g Z) (g T) r) (regularForm (f X) (f Y) t) := by
    rw [←map_regularForm f X Y (pow_cutoff_eq_zero F hX),
      ←map_regularForm g Z T (pow_cutoff_eq_zero G hZ)]
    exact (hc _ _).symm
  rw [map_normalized_general f F H hX hY hfX hfY hs.le hs1,
    map_normalized_general g G H hZ hT hgZ hgT hs.le hs1]
  simp only [normalizedSolution,gauge_add_of_commute (hc X Z)]
  rw [show regularForm (f X+g Z) (f Y+g T)=(fun r => regularForm (f X) (f Y) r+regularForm (g Z) (g T) r) from funext hreg]
  rw [transport_add_commute H (regularForm_mem H hfX hfY) (regularForm_mem H hgZ hgT) hs
    (regularForm_integrable (f X) (f Y) hfn hs.le hs1)
    (regularForm_integrable (g Z) (g T) hgn hs.le hs1)
    (regularForm_continuous _ _ hs1.le) (regularForm_continuous _ _ hs1.le) hcomm]
  have ht : Commute (gauge (g Z) s) (transport (regularForm (f X) (f Y)) 0 H.cutoff s) := by
    apply transport_commute
    intro r
    rw [←map_gauge g Z (pow_cutoff_eq_zero G hZ),←map_regularForm f X Y (pow_cutoff_eq_zero F hX)]
    exact (hc _ _).symm
  exact ht.mul_mul_mul_comm _ _

 theorem associator_product (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    (H : NilpotentFiltration C) {X Y : A} {Z T : B}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈G.space 1) (hT : T∈G.space 1)
    (hfX : f X∈H.space 1) (hfY : f Y∈H.space 1)
    (hgZ : g Z∈H.space 1) (hgT : g T∈H.space 1) :
    associator H (f X+g Z) (f Y+g T)=f (associator F X Y)*g (associator G Z T) := by
  have h₁ := normalized_sum f g hc F G H hX hY hZ hT hfX hfY hgZ hgT
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have h₂ := normalized_sum f g hc F G H hY hX hT hZ hfY hfX hgT hgZ
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  simp only [KZCollar.associator,rightSolution,show (1:ℝ)-1/2=1/2 by norm_num]
  rw [h₁,h₂]
  have hu := (normalizedSolution_isUnit G hT hZ (1/2)).map g
  rw [Ring.inverse_mul (Or.inr hu),←map_unit_inverse f (normalizedSolution_isUnit F hY hX (1/2)),
    ←map_unit_inverse g (normalizedSolution_isUnit G hT hZ (1/2)),
    (hc (Ring.inverse (normalizedSolution F Y X (1/2))) (Ring.inverse (normalizedSolution G T Z (1/2)))).eq.symm,
    shuffle f g hc]

end KZProduct

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

theorem coeff_gauge_Y (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) (p : Q ℝ N) (s : ℝ) :
    c N m (gauge (-Y N) s*p)=c N m p := by
  have hy : (-Y N)^(N+1)=0 := by
    have hh : Y N^(N+1)=0 := pow_cutoff_eq_zero (weight N) (gen_weight N true)
    rw [neg_pow,hh,mul_zero]
  rw [gauge_finite _ hy,Finset.sum_mul,map_sum,Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [smul_mul_assoc,map_smul,neg_pow]
    have he : (-1:Q ℝ N)^i * Y N^i *p = (-1:ℝ)^i • (Y N^i*p) := by
      simp only [Algebra.smul_def,map_pow,map_neg,map_one]
      noncomm_ring
    rw [he,map_smul]
    change _ • (_ • (coeff N (GenericIhara.depthOneWord m) (gen N true^i*p)))=0
    rw [coeff_Y_prefix N i m hN hm,ite_eq_right hi0,smul_zero,smul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ N)))

def prefactor (m i : ℕ) (s : ℝ) : ℝ :=
  (Real.log s^i/(i.factorial:ℝ)) *
    if i ≤ m then -(1/((m-i).factorial:ℝ))*(∫ t in (0:ℝ)..s,DepthIntegral.kernel (m-i) t) else 0

theorem coeff_normalized (N m : ℕ) (hN : m+1 ≤ N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    c N m (normalizedSolution (weight N) (X N) (Y N) s)=
      ∑ i∈Finset.range (N+1),prefactor m i s := by
  rw [normalizedSolution,gauge_finite _ (X_nilpotent N),Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_mul_assoc,map_smul]
  change (Real.log s^i/(i.factorial:ℝ))*(coeff N (GenericIhara.depthOneWord m)
    (gen N false^i*transport (regularForm (X N) (Y N)) 0 N s))=_
  rw [coeff_prefix N i m hN]
  unfold prefactor
  split_ifs with him
  · congr 1
    exact coeff_transport N (m-i) (by omega) h0 h1
  · rfl

theorem prefactor_limit (m i : ℕ) (hm : 0 < m) :
    Tendsto (prefactor m i) (𝓝[<] 1)
      (𝓝 (if i=0 then -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t) else 0)) := by
  change Tendsto (fun s => prefactor m i s) _ _
  have hl : Tendsto Real.log (𝓝[<] (1:ℝ)) (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  by_cases hi : i=0
  · subst i
    simpa only [prefactor,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.zero_le,
      ↓reduceIte,Nat.sub_zero,one_mul] using
      (tendsto_const_nhds (x:= -(1/(m.factorial:ℝ)))).mul (DepthIntegral.integral_limit m hm)
  · rw [ite_eq_right hi]
    by_cases him : i ≤ m
    · by_cases him' : i=m
      · subst i
        have hh := (DepthIntegral.log_endpoint_product m hm).div_const (m.factorial:ℝ)
        simp only [zero_div] at hh
        apply hh.congr'
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
        unfold prefactor
        rw [ite_eq_left (le_refl m),Nat.sub_self,DepthIntegral.integral_zero hs0.le hs]
        simp only [Nat.factorial_zero,Nat.cast_one,div_one]
        ring
      · have hpos : 0 < m-i := by omega
        have hpow : Tendsto (fun s : ℝ => Real.log s^i/(i.factorial:ℝ)) (𝓝[<] 1) (𝓝 0) := by
          simpa only [zero_pow hi,zero_div] using (hl.pow i).div_const (i.factorial:ℝ)
        have h := hpow.mul ((tendsto_const_nhds (x:= -(1/((m-i).factorial:ℝ)))).mul
          (DepthIntegral.integral_limit (m-i) hpos))
        simpa only [prefactor,ite_eq_left him,zero_mul] using h
    · simp only [prefactor,ite_eq_right him,mul_zero]
      exact tendsto_const_nhds

theorem coeff_normalized_limit (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    Tendsto (fun s => c N m (normalizedSolution (weight N) (X N) (Y N) s)) (𝓝[<] 1)
      (𝓝 (-(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t))) := by
  have hh := tendsto_finsetSum (Finset.range (N+1)) (fun i _ => prefactor_limit m i hm)
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,↓reduceIte] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  exact (coeff_normalized N m hN hs0.le hs).symm

theorem left_regularized_limit (N : ℕ) :
    Tendsto (fun s => gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s)
      (𝓝[<] 1) (𝓝 (associator (weight N) (X N) (Y N))) := by
  have hh := ((regularTransport_limit (Y:=X N) (weight N) (gen_weight N true)).comp
    DepthIntegral.one_sub_limit).mul (tendsto_const_nhds (x:=associator (weight N) (X N) (Y N)))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  rw [left_eq_right_mul_associator (weight N) (gen_weight N false) (gen_weight N true) ⟨hs0,hs⟩]
  simp only [rightSolution,normalizedSolution,←mul_assoc,gauge_neg_mul,one_mul,Function.comp_apply]

theorem associator_coefficient (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    c N m (associator (weight N) (X N) (Y N))=
      -(1/(m.factorial:ℝ))*(∫ t in (0:ℝ)..1,DepthIntegral.kernel m t) := by
  have hh := (c N m).toContinuousLinearMap.continuous.tendsto
    (associator (weight N) (X N) (Y N)) |>.comp (left_regularized_limit N)
  have he : (fun s => c N m (gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s))=
      (fun s => c N m (normalizedSolution (weight N) (X N) (Y N) s)) := by
    funext s
    exact coeff_gauge_Y N m hN hm _ _
  change Tendsto (fun s => c N m (gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s)) _ _ at hh
  rw [he] at hh
  exact tendsto_nhds_unique hh (coeff_normalized_limit N m hN hm)

theorem associator_coefficient_ne_zero (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    c N m (associator (weight N) (X N) (Y N))≠0 := by
  rw [associator_coefficient N m hN hm]
  exact DepthIntegral.coefficient_ne_zero m hm

 theorem depth_initial (N : ℕ) : depthSpace (R:=ℝ) N 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ
    (TruncatedWords.relations (∅ : Set (AssociativeElimination.A ℝ Bool)) N) u
  exact ⟨p,WordGrading.mem_space (by intros; exact Nat.zero_le _),rfl⟩

 theorem gaugeX_depth_zero (N : ℕ) (s : ℝ) : KZCollar.gauge (X N) s∈depthSpace N 0 := by
  rw [depth_initial]; trivial

 theorem left_regularized_depth (N : ℕ) (s : ℝ) :
    KZCollar.gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s-KZCollar.gauge (X N) s∈depthSpace N 1 := by
  have hg := gauge_sub_one_mem (depth N) ((depthSpace N 1).neg_mem (gen_depth N true)) (1-s)
  have ht : transport (regularForm (X N) (Y N)) 0 N s-1∈depthSpace N 1 :=
    transport_sub_one_mem (depth N) (regularForm_depth N) 0 s N
  have hnorm : normalizedSolution (weight N) (X N) (Y N) s∈depthSpace N 0 := by
    rw [depth_initial]; trivial
  have h := (depthSpace N 1).add_mem (depth_mul N 1 0 hg hnorm)
    (depth_mul N 0 1 (gaugeX_depth_zero N s) ht)
  have he : KZCollar.gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s-KZCollar.gauge (X N) s=
      (KZCollar.gauge (-Y N) (1-s)-1)*normalizedSolution (weight N) (X N) (Y N) s+
      KZCollar.gauge (X N) s*(transport (regularForm (X N) (Y N)) 0 N s-1) := by
    unfold normalizedSolution
    change KZCollar.gauge (-Y N) (1-s)*(KZCollar.gauge (X N) s*transport (regularForm (X N) (Y N)) 0 N s)-KZCollar.gauge (X N) s=_
    change _= (KZCollar.gauge (-Y N) (1-s)-1)*(KZCollar.gauge (X N) s*transport (regularForm (X N) (Y N)) 0 N s)+_
    noncomm_ring
  rwa [he]

 theorem associator_depth_one (N : ℕ) :
    associator (weight N) (X N) (Y N)-1∈depthSpace N 1 := by
  have hg : Tendsto (KZCollar.gauge (X N)) (𝓝[<] (1:ℝ)) (𝓝 (1:Q ℝ N)) := by
    have hh := (gauge_derivative (X N) (s:=1) one_ne_zero).continuousAt.tendsto.mono_left
      (show 𝓝[<] (1:ℝ)≤𝓝 (1:ℝ) from nhdsWithin_le_nhds)
    simpa only [KZCollar.gauge,Real.log_one,zero_smul,NormedSpace.exp_zero] using hh
  exact (depthSpace (R:=ℝ) N 1).closed_of_finiteDimensional.mem_of_tendsto
    ((left_regularized_limit N).sub hg) (Eventually.of_forall (left_regularized_depth N))

end CutoffKZ

namespace ConjugateComparison

section
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem mem_zero (u : Q) : u∈F 0 := by rw [filtration_initial]; trivial

theorem inverse_normalized (P : Qˣ) (hP : (P:Q)-1∈F 1) : ((P⁻¹:Qˣ):Q)-1∈F 1 := by
  have h := filtration_mul ∅ N 0 1 (mem_zero N ((P⁻¹:Qˣ):Q)) hP
  have he : ((P⁻¹:Qˣ):Q)*((P:Q)-1)=-(((P⁻¹:Qˣ):Q)-1) := by
    rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
  rw [he] at h
  exact (F 1).neg_mem_iff.mp h

def family (P : Qˣ) : Bool → Q
  | false => gen N false
  | true => ((P⁻¹:Qˣ):Q)*gen N true*(P:Q)

theorem family_mem (P : Qˣ) (b : Bool) : family N P b∈F 1 := by
  cases b
  · exact gen_mem N false
  · exact filtration_mul ∅ N 1 0
      (filtration_mul ∅ N 0 1 (mem_zero N _) (gen_mem N true)) (mem_zero N _)

theorem family_leading (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    family N P b-gen N b∈F 2 := by
  cases b
  · simp only [family,sub_self,Submodule.zero_mem]
  · have hh := (F 2).sub_mem
      (filtration_mul ∅ N 1 1 (gen_mem N true) hP)
      (filtration_mul ∅ N 1 1 hP (gen_mem N true))
    have hi := filtration_mul ∅ N 0 2 (mem_zero N ((P⁻¹:Qˣ):Q)) hh
    have he : ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)=
        family N P true-gen N true := by
      simp only [family,mul_sub,sub_mul,mul_one,one_mul]
      rw [←mul_assoc ((P⁻¹:Qˣ):Q) (P:Q),Units.inv_mul,one_mul]
      rw [mul_assoc]
      abel
    rwa [he] at hi

def transport (P : Qˣ) (hP : (P:Q)-1∈F 1) : Q ≃ₐ[R] Q :=
  equiv N (family N P) (family_mem N P) (family_leading N P hP)

@[simp] theorem transport_gen (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := subst_gen N _ _ b

def theta (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) : Q ≃ₐ[R] Q :=
  (transport N P hP).symm.trans (transport N V hV)

def unitArrow (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) : Qˣ :=
  V*(Units.map (theta N P V hP hV).toMonoidHom P)⁻¹

theorem exact_comparison (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)*theta N P V hP hV (P:Q)=(V:Q) := by
  change ((V:Q)*((Units.map (theta N P V hP hV).toMonoidHom P)⁻¹:Qˣ))*
    (Units.map (theta N P V hP hV).toMonoidHom P:Q)=(V:Q)
  rw [mul_assoc,Units.inv_mul,mul_one]

theorem theta_transport (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) (u : Q) :
    theta N P V hP hV (transport N P hP u)=transport N V hV u := by
  exact congrArg (transport N V hV) ((transport N P hP).symm_apply_apply u)

theorem theta_x (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N false)=gen N false := by
  simpa only [transport_gen,family] using theta_transport N P V hP hV (gen N false)

theorem theta_y (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N true)=
      (((unitArrow N P V hP hV)⁻¹:Qˣ):Q)*gen N true*(unitArrow N P V hP hV:Q) := by
  have hh := theta_transport N P V hP hV (gen N true)
  simp only [transport_gen,family,map_mul] at hh
  let M := Units.map (theta N P V hP hV).toMonoidHom P
  have h : ((M⁻¹:Qˣ):Q)*theta N P V hP hV (gen N true)*(M:Q)=
      ((V⁻¹:Qˣ):Q)*gen N true*(V:Q) := hh
  have hh := congrArg (fun z : Q => (M:Q)*z*((M⁻¹:Qˣ):Q)) h
  simp only [mul_assoc,Units.mul_inv_cancel_left] at hh
  simpa only [unitArrow,mul_inv_rev,inv_inv,Units.val_mul,M,mul_assoc,Units.mul_inv,mul_one] using hh

end

open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem transport_raises (P : Qˣ) (hP : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    transport N P hP u-u∈F (n+1) :=
  subst_raises N (family N P) (family_mem N P) (family_leading N P hP) n u hu

theorem transport_inverse_preserves (P : Qˣ) (hP : (P:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : (transport N P hP).symm u∈F n := by
  have hh : ∀ k≤n,(transport N P hP).symm u∈F k := by
    intro k
    induction k with
    | zero => intro _; exact mem_zero N _
    | succ k ih =>
      intro hk
      have hd := transport_raises N P hP k _ (ih (by omega))
      rw [AlgEquiv.apply_symm_apply] at hd
      have he := (F (k+1)).sub_mem (filtration_antitone ∅ N hk hu) hd
      simpa only [sub_sub_cancel] using he
  exact hh n le_rfl

theorem theta_raises (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u-u∈F (n+1) := by
  have hh := transport_inverse_preserves N P hP n u hu
  have hd := (F (n+1)).sub_mem (transport_raises N V hV n _ hh)
    (transport_raises N P hP n _ hh)
  simpa only [sub_sub_sub_cancel_right,AlgEquiv.apply_symm_apply,theta,AlgEquiv.trans_apply] using hd

theorem theta_preserves (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u∈F n := by
  have h := (F n).add_mem (filtration_antitone ∅ N (Nat.le_succ n)
    (theta_raises N P V hP hV n u hu)) hu
  simpa only [sub_add_cancel] using h

theorem mul_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    ((P*V:Qˣ):Q)-1∈F 1 := by
  have h := (F 1).add_mem
    (filtration_mul ∅ N 1 0 hP (mem_zero N (V:Q))) hV
  simpa only [sub_mul,one_mul,sub_add_sub_cancel,Units.val_mul] using h

theorem unitArrow_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)-1∈F 1 := by
  apply mul_normalized N V _ hV
  apply inverse_normalized N
  change theta N P V hP hV (P:Q)-1∈_
  simpa only [map_sub,map_one] using theta_preserves N P V hP hV 1 ((P:Q)-1) hP

end ConjugateComparison

namespace DepthSubstitution
open AssociativeElimination WordGrading TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => CutoffDepth.Q R N
local notation "F" => CutoffDepth.depthSpace (R:=R) N

 theorem initial : F 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R Bool)) N) u
  exact ⟨p,mem_space (by intros; exact Nat.zero_le _),rfl⟩

 theorem all_zero (u : Q) : u∈F 0 := by rw [initial]; trivial

 theorem lift_word_mem (f : Bool → Q) (hf : ∀ a,f a∈F (GenericIhara.depth a)) (w : FreeMonoid Bool) :
    lift (R:=R) f (word w)∈F (degree GenericIhara.depth w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using CutoffDepth.depth_one (R:=R) N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact CutoffDepth.depth_mul N _ _ (hf a) ih

 theorem lift_word_difference (f g : Bool → Q)
    (hf : ∀ a,f a∈F (GenericIhara.depth a)) (hg : ∀ a,g a∈F (GenericIhara.depth a))
    (hd : ∀ a,f a-g a∈F (GenericIhara.depth a+1)) (w : FreeMonoid Bool) :
    lift (R:=R) f (word w)-lift (R:=R) g (word w)∈F (degree GenericIhara.depth w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,map_mul,lift_atom,lift_atom,degree_mul,degree_of]
    have he : f a*lift (R:=R) f (word w)-g a*lift (R:=R) g (word w)=
        (f a-g a)*lift (R:=R) g (word w)+f a*(lift (R:=R) f (word w)-lift (R:=R) g (word w)) := by
      rw [sub_mul,mul_sub]; abel
    rw [he]
    exact (F _).add_mem
      (by simpa only [Nat.add_right_comm] using CutoffDepth.depth_mul N _ _ (hd a) (lift_word_mem N g hg w))
      (by simpa only [Nat.add_assoc] using CutoffDepth.depth_mul N _ _ (hf a) ih)

 theorem subst_raises (f : Bool → Q)
    (hw : ∀ a,f a∈filtration ∅ N 1)
    (hf : ∀ a,f a∈F (GenericIhara.depth a))
    (hd : ∀ a,f a-gen N a∈F (GenericIhara.depth a+1))
    (n : ℕ) (u : Q) (hu : u∈F n) : subst N f hw u-u∈F (n+1) := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hw (quotient ∅ N p)-quotient ∅ N p∈_
  rw [subst_quotient]
  have hh := map_space ((lift (R:=R) f).toLinearMap-(lift (R:=R) (gen N)).toLinearMap) _
    (fun w hw => CutoffDepth.depth_antitone N (Nat.add_le_add_right hw 1)
      (lift_word_difference N f (gen N) hf (CutoffDepth.gen_depth N) hd w)) hp
  simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,lift_gen] using hh

 theorem family_mem (P : Qˣ) (b : Bool) : ConjugateComparison.family N P b∈F (GenericIhara.depth b) := by
  cases b
  · exact CutoffDepth.gen_depth N false
  · exact CutoffDepth.depth_mul N 1 0
      (CutoffDepth.depth_mul N 0 1 (all_zero N _) (CutoffDepth.gen_depth N true)) (all_zero N _)

 theorem family_leading (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    ConjugateComparison.family N P b-gen N b∈F (GenericIhara.depth b+1) := by
  cases b
  · simp only [ConjugateComparison.family,sub_self,Submodule.zero_mem]
  · have hh := (F 2).sub_mem
      (CutoffDepth.depth_mul N 1 1 (CutoffDepth.gen_depth N true) hP)
      (CutoffDepth.depth_mul N 1 1 hP (CutoffDepth.gen_depth N true))
    have hi := CutoffDepth.depth_mul N 0 2 (all_zero N ((P⁻¹:Qˣ):Q)) hh
    have he : ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)=
        ConjugateComparison.family N P true-gen N true := by
      simp only [ConjugateComparison.family,mul_sub,sub_mul,mul_one,one_mul]
      rw [←mul_assoc ((P⁻¹:Qˣ):Q) (P:Q),Units.inv_mul,one_mul]
      rw [mul_assoc]
      abel
    change ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)∈F 2 at hi
    rwa [he] at hi

end DepthSubstitution

namespace CutoffScaling
open AssociativeElimination WordGrading TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] {α : Type*} (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R α)) N

 def map (r : R) : Q →ₐ[R] Q := subst N (fun a => r • gen N a)
  (fun a => (filtration ∅ N 1).smul_mem r (gen_mem N a))

 @[simp] theorem map_gen (r : R) (a : α) : map N r (gen N a)=r • gen N a := subst_gen N _ _ a

 theorem lift_word (r : R) (w : FreeMonoid α) :
    lift (R:=R) (fun a => r • gen (R:=R) N a) (word w)=r^(degree wt w) • quotient (∅ : Set (A R α)) N (word w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,map_mul,word_of,lift_atom,ih,degree_mul,degree_of]
    change (r • gen N a)*(r^degree wt w • quotient ∅ N (word w))=r^(1+degree wt w) • quotient ∅ N (atom a*word w)
    rw [pow_add,pow_one,map_mul,smul_mul_assoc,mul_smul_comm,smul_smul]
    rfl

 theorem map_word (r : R) (w : FreeMonoid α) :
    map N r (quotient ∅ N (word w))=r^(degree wt w) • quotient ∅ N (word w) := by
  rw [map,subst_quotient,lift_word]

 theorem coefficient (r : R) (w : FreeMonoid α) (u : Q) :
    TruncatedFree.coefficient N w (map N r u)=r^(degree wt w)*TruncatedFree.coefficient N w u := by
  classical
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  change TruncatedFree.coefficient N w (map N r (quotient ∅ N p))=_
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change TruncatedFree.coefficient N w (map N r (quotient ∅ N (word v)))=r^(degree wt w)*TruncatedFree.coefficient N w (quotient ∅ N (word v))
    rw [map_word,map_smul]
    simp only [TruncatedFree.coefficient_quotient,smul_eq_mul]
    by_cases he : v=w
    · subst v; rfl
    · have hn : (word (R:=R) v).coeff w=0 := by simp [word,he]
      simp only [hn,ite_self,mul_zero]
  | add p q hp hq => simp only [map_add,hp,hq,mul_add]
  | smul s p hp => simp only [map_smul,hp,smul_eq_mul]; ring

 theorem preserves_depth (r : R) (n : ℕ) (u : TruncatedWords.Q (∅ : Set (A R Bool)) N)
    (hu : u∈CutoffDepth.depthSpace N n) : map N r u∈CutoffDepth.depthSpace N n := by
  obtain ⟨p,hp,rfl⟩ := hu
  change map N r (quotient ∅ N p)∈_
  rw [map,subst_quotient]
  apply map_space (lift (R:=R) (fun a => r • gen N a)).toLinearMap _ (fun w hw => ?_) hp
  change lift (R:=R) (fun a => r • gen N a) (word w)∈CutoffDepth.depthSpace N n
  rw [lift_word]
  exact (CutoffDepth.depthSpace N n).smul_mem _ ⟨word w,word_mem w hw,rfl⟩

end CutoffScaling

namespace ConjugateComparison
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => CutoffDepth.Q R N
local notation "F" => CutoffDepth.depthSpace (R:=R) N

 theorem transport_depth_raises (P : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hPd : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    transport N P hP u-u∈F (n+1) :=
  DepthSubstitution.subst_raises N (family N P) (family_mem N P)
    (DepthSubstitution.family_mem N P) (DepthSubstitution.family_leading N P hPd) n u hu

 theorem transport_inverse_depth (P : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hPd : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    (transport N P hP).symm u∈F n := by
  have hh : ∀ k≤n,(transport N P hP).symm u∈F k := by
    intro k
    induction k with
    | zero => intro _; exact DepthSubstitution.all_zero N _
    | succ k ih =>
      intro hk
      have hd := transport_depth_raises N P hP hPd k _ (ih (by omega))
      rw [AlgEquiv.apply_symm_apply] at hd
      have he := (F (k+1)).sub_mem (CutoffDepth.depth_antitone N hk hu) hd
      simpa only [sub_sub_cancel] using he
  exact hh n le_rfl

 theorem theta_depth_raises (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u-u∈F (n+1) := by
  have hh := transport_inverse_depth N P hP hPd n u hu
  have hd := (F (n+1)).sub_mem (transport_depth_raises N V hV hVd n _ hh)
    (transport_depth_raises N P hP hPd n _ hh)
  simpa only [sub_sub_sub_cancel_right,AlgEquiv.apply_symm_apply,theta,AlgEquiv.trans_apply] using hd

 theorem theta_depth_preserves (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u∈F n := by
  have h := (F n).add_mem (CutoffDepth.depth_antitone N (Nat.le_succ n)
    (theta_depth_raises N P V hP hV hPd hVd n u hu)) hu
  simpa only [sub_add_cancel] using h

 theorem units_product_depth (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    ((P*V:Qˣ):Q)-1∈F 1 := by
  have h := (F 1).add_mem (CutoffDepth.depth_mul N 1 0 hP (DepthSubstitution.all_zero N (V:Q))) hV
  simpa only [sub_mul,one_mul,sub_add_sub_cancel,Units.val_mul] using h

 theorem units_inverse_depth (P : Qˣ) (hP : (P:Q)-1∈F 1) : ((P⁻¹:Qˣ):Q)-1∈F 1 := by
  have h := CutoffDepth.depth_mul N 0 1 (DepthSubstitution.all_zero N ((P⁻¹:Qˣ):Q)) hP
  have he : ((P⁻¹:Qˣ):Q)*((P:Q)-1)= -(((P⁻¹:Qˣ):Q)-1) := by
    rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
  rw [he] at h
  exact (F 1).neg_mem_iff.mp h

 theorem unitArrow_depth (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)-1∈F 1 := by
  apply units_product_depth N V _ hVd
  apply units_inverse_depth N
  change theta N P V hP hV (P:Q)-1∈_
  simpa only [map_sub,map_one] using theta_depth_preserves N P V hP hV hPd hVd 1 ((P:Q)-1) hPd

end ConjugateComparison

end DeligneDrinfeld

end

end OAI
