import Mathlib
import OAI.Analysis.HardSphere.Geometry.EnnrealTsumFinset
import OAI.Analysis.HardSphere.Geometry.NominalDrift

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

def endpointDanger {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K)) (x : DiscreteTorus K) : Prop :=
  ∃ F∈candidateSets (torusRangeGraph K 1), F⊆B ∧ ∃ c∈F, torusNear K F.card x c

lemma fill_endpoint_danger {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (r x : Vertex) (hr : torusProjection K r∈B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K r)).card<K)
    (C : Finset Vertex)
    (hC : (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r)
    (hx : x∉exterior C) : endpointDanger B (torusProjection K x) := by
  let F := badComponent (torusRangeGraph K 1) B (torusProjection K r)
  have hrF : torusProjection K r∈F := mem_own_badComponent _ _ hr
  obtain ⟨D,hD,_,hspan⟩ := small_periodic_lifts (a:=1) (by simpa using hK) F
    (by simpa using hsmall) (badComponent_preconnected _ _ _) r hrF
  have hCD : C=D := Finset.coe_injective (hC.trans hD.symm)
  subst D
  have hrC : r∈C := by change r∈(↑C:Set Vertex); rw [hC]; exact ⟨hrF,.refl⟩
  have hbox := fill_subset_coordinateBox C (show x∈fill C from hx)
  have hbound (i : Fin 3) : |x i-r i|≤F.card := by
    obtain ⟨⟨l,hl,hlx⟩,⟨u,hu,hxu⟩⟩ := hbox i
    have hlow := hspan l hl r hrC i
    have hhigh := hspan u hu r hrC i
    obtain ⟨hlow₁,hlow₂⟩ := abs_le.mp hlow
    obtain ⟨hhigh₁,hhigh₂⟩ := abs_le.mp hhigh
    exact abs_le.mpr ⟨by omega,by omega⟩
  refine ⟨F,badComponents_candidate _ B (Finset.mem_image.mpr ⟨torusProjection K r,hr,rfl⟩),
    badComponent_subset _ B _,torusProjection K r,hrF,projection_near hbound⟩

lemma endpointsExterior_of_no_danger {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hsmall : ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K)
    (hv : ¬endpointDanger B (torusProjection K v)) (hw : ¬endpointDanger B (torusProjection K w)) :
    endpointsExterior B v w := by
  intro r hr C hC
  constructor
  · by_contra hn
    exact hv (fill_endpoint_danger hK B r v hr (hsmall _ hr) C hC hn)
  · by_contra hn
    exact hw (fill_endpoint_danger hK B r w hr (hsmall _ hr) C hC hn)

def acceptedEnvironment {K : ℕ} [NeZero K] (a : ℕ) (B : Finset (DiscreteTorus K)) (v w : Vertex) : Prop :=
  ¬LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) ∧ endpointsExterior B v w

lemma small_star_of_no_large {K a : ℕ} [NeZero K] (ha : 1≤a)
    (B : Finset (DiscreteTorus K)) (hB : ¬LargeBadComponent (torusRangeGraph K a) B (K/(10*a))) :
    ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K := by
  intro z hz
  have hC : badComponent (torusRangeGraph K a) B z∈badComponents (torusRangeGraph K a) B :=
    Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hcard : (badComponent (torusRangeGraph K a) B z).card<K/(10*a) := by
    by_contra hn
    exact hB ⟨_,hC,by omega⟩
  have hsub : badComponent (torusRangeGraph K 1) B z ⊆ badComponent (torusRangeGraph K a) B z := by
    intro y hy
    rcases (mem_badComponent _ _ _ _).mp hy with ⟨hyB,hzy⟩
    exact (mem_badComponent _ _ _ _).mpr ⟨hyB,hzy.mono (badGraph_graphMono (torusRangeGraph_mono ha) B)⟩
  exact (Finset.card_le_card hsub).trans_lt (hcard.trans_le (Nat.div_le_self _ _))

lemma rejection_subset {K a : ℕ} [NeZero K] (hK : 2<K) (ha : 1≤a)
    (B : Finset (DiscreteTorus K)) (v w : Vertex) (hE : ¬acceptedEnvironment a B v w) :
    LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) ∨
      endpointDanger B (torusProjection K v) ∨ endpointDanger B (torusProjection K w) := by
  by_contra h
  push Not at h
  apply hE
  exact ⟨h.1,endpointsExterior_of_no_danger hK B v w (small_star_of_no_large ha B h.1) h.2.1 h.2.2⟩

def endpointAnimals {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ) : Finset (Finset (DiscreteTorus K)) :=
  (torusBall m x).biUnion (fun c ↦ rootedAnimals (torusRangeGraph K 1) c m)

lemma endpointAnimals_card {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ) :
    (endpointAnimals x m).card≤(2*m+1)^3*(2^27)^m := by
  calc
    _ ≤ ∑ c∈torusBall m x, (rootedAnimals (torusRangeGraph K 1) c m).card := Finset.card_biUnion_le
    _ ≤ ∑ _c∈torusBall m x, (2^27)^m := by
      apply Finset.sum_le_sum
      intro c _
      exact rootedAnimals_card_le _ 27 (by simpa using torusRange_degree (K:=K) 1) c m
    _ = (torusBall m x).card*(2^27)^m := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (torusNear_ball_card _ _)

lemma mem_endpointAnimals_card {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ)
    {F : Finset (DiscreteTorus K)} (hF : F∈endpointAnimals x m) : F.card=m := by
  obtain ⟨c,_,hF⟩ := Finset.mem_biUnion.mp hF
  exact (Finset.mem_filter.mp hF).2.2.1

lemma danger_contains_endpointAnimal {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    (x : DiscreteTorus K) (h : endpointDanger B x) :
    ∃ m : ℕ, ∃ F∈endpointAnimals x (m+1), F⊆B := by
  obtain ⟨F,hF,hFB,c,hc,hxc⟩ := h
  have hpos := Finset.card_pos.mpr (candidate_nonempty _ hF)
  have hcard : F.card-1+1=F.card := by omega
  refine ⟨F.card-1,F,?_,hFB⟩
  rw [hcard]
  exact Finset.mem_biUnion.mpr ⟨c,(mem_torusBall _ _ _).mpr hxc,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,rfl,fun y hy ↦ candidate_reach _ hF hc hy⟩⟩

theorem endpointDanger_probability {K : ℕ} [NeZero K]
    (μ : PMF (Finset (DiscreteTorus K))) (p : ℝ≥0∞) (hbad : JointBadLaw μ p) (x : DiscreteTorus K) :
    (∑' B, if endpointDanger B x then μ B else 0) ≤
      ∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*(((2^27:ℕ):ℝ≥0∞)*p)^(m+1) := by
  have hpoint (B : Finset (DiscreteTorus K)) :
      (if endpointDanger B x then μ B else 0) ≤
      ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), if F⊆B then μ B else 0 := by
    by_cases h : endpointDanger B x
    · obtain ⟨m,F,hF,hFB⟩ := danger_contains_endpointAnimal B x h
      rw [ite_eq_left h]
      exact le_trans (by
        simpa only [ite_eq_left hFB] using
          (Finset.single_le_sum (f := fun F : Finset (DiscreteTorus K) ↦ if F⊆B then μ B else 0)
            (fun _ _ ↦ zero_le) hF)) (ENNReal.le_tsum m)
    · rw [ite_eq_right h]; exact zero_le
  calc
    _ ≤ ∑' B, ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), if F⊆B then μ B else 0 := ENNReal.tsum_le_tsum hpoint
    _ = ∑' m : ℕ, ∑ F∈endpointAnimals x (m+1), ∑' B, if F⊆B then μ B else 0 := by
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun m ↦ ennreal_tsum_finset _ _
    _ ≤ ∑' m : ℕ, ∑ _F∈endpointAnimals x (m+1), p^(m+1) := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply Finset.sum_le_sum
      intro F hF
      simpa only [mem_endpointAnimals_card x (m+1) hF] using hbad F
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro m
      simp only [Finset.sum_const,nsmul_eq_mul]
      calc
        _ ≤ (((2*(m+1)+1)^3*(2^27)^(m+1):ℕ):ℝ≥0∞)*p^(m+1) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast endpointAnimals_card x (m+1)
        _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

open scoped NNReal
lemma endpoint_polynomial_le (m : ℕ) : (2*(m+1)+1)^3≤27*8^m := by
  have hs : m+1≤2^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      have hp := Nat.one_le_pow m 2 (by norm_num)
      omega
  calc
    _ ≤ (3*2^m)^3 := Nat.pow_le_pow_left (by nlinarith) 3
    _ = _ := by rw [mul_pow,← pow_mul,Nat.mul_comm m 3,pow_mul]; norm_num

lemma endpoint_series_le (q : ℝ≥0∞) (hq : q≤1/16) :
    (∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*q^(m+1))≤54*q := by
  have h8 : (8:ℝ≥0∞)*q≤1/2 := by
    calc
      _ ≤ 8*(1/16:ℝ≥0∞) := mul_le_mul' le_rfl hq
      _ = _ := by
        have h : (8:ℝ≥0)*(1/16)=1/2 := by norm_num
        have hh := congrArg (fun x : ℝ≥0 ↦ (x:ℝ≥0∞)) h
        simpa only [ENNReal.coe_mul,ENNReal.coe_div (show (16:ℝ≥0)≠0 by norm_num),
          ENNReal.coe_div (show (2:ℝ≥0)≠0 by norm_num),ENNReal.coe_ofNat,ENNReal.coe_one] using hh
  calc
    _ ≤ ∑' m : ℕ, 27*q*((1/2:ℝ≥0∞)^m) := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ (27*8^m:ℝ≥0∞)*q^(m+1) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast endpoint_polynomial_le m
        _ = 27*q*((8*q)^m) := by rw [pow_succ,mul_pow]; ring
        _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' h8 m)
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]; norm_num; ring

lemma rejection_probability {K a : ℕ} [NeZero K] (hK : 2<K) (ha : 1≤a)
    (hm : 1≤K/(10*a)) (μ : PMF (Finset (DiscreteTorus K))) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (v w : Vertex) :
    (∑' B, if ¬acceptedEnvironment a B v w then μ B else 0)≤
      (K:ℝ≥0∞)^3*(((2^((2*a+1)^3):ℕ):ℝ≥0∞)*p)^(K/(10*a))+
      2*∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*(((2^27:ℕ):ℝ≥0∞)*p)^(m+1) := by
  have hpoint (B : Finset (DiscreteTorus K)) :
      (if ¬acceptedEnvironment a B v w then μ B else 0)≤
      (if LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) then μ B else 0)+
      (if endpointDanger B (torusProjection K v) then μ B else 0)+
      (if endpointDanger B (torusProjection K w) then μ B else 0) := by
    by_cases hE : ¬acceptedEnvironment a B v w
    · rw [ite_eq_left hE]
      rcases rejection_subset hK ha B v w hE with h|h|h
      · rw [ite_eq_left h]; exact le_add_of_le_left le_self_add
      · rw [ite_eq_left h]; exact le_add_of_le_left le_add_self
      · rw [ite_eq_left h]; exact le_add_self
    · rw [ite_eq_right hE]; exact zero_le
  calc
    _ ≤ _ := ENNReal.tsum_le_tsum hpoint
    _ = _ := by rw [ENNReal.tsum_add,ENNReal.tsum_add]
    _ ≤ _ := add_le_add (add_le_add
      (largeBadComponent_probability (torusRangeGraph K a) ((2*a+1)^3)
        (torusRange_degree a) μ p hbad (K/(10*a)) hm)
      (endpointDanger_probability μ p hbad (torusProjection K v)))
      (endpointDanger_probability μ p hbad (torusProjection K w))
    _ = _ := by
      simp only [DiscreteTorus,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow]
      ring

lemma large_rejection_eventually (a : ℕ) (ha : 1≤a) :
    ∀ᶠ K : ℕ in Filter.atTop, (K:ℝ)^3*(1/2:ℝ)^(K/(10*a))≤1/4 := by
  let d := 10*a
  have hd : 0<d := by dsimp [d]; omega
  have hl := tendsto_pow_const_mul_const_pow_of_lt_one 3 (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hlim : Filter.Tendsto (fun j : ℕ ↦ ((2*d:ℕ):ℝ)^3*((j:ℝ)^3*(1/2:ℝ)^j)) Filter.atTop (nhds 0) := by
    simpa using hl.const_mul (((2*d:ℕ):ℝ)^3)
  have hSmall : ∀ᶠ j : ℕ in Filter.atTop,
      ((2*d:ℕ):ℝ)^3*((j:ℝ)^3*(1/2:ℝ)^j)≤1/4 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ h ↦ h.le)
  have hdiv := Nat.tendsto_div_const_atTop (ne_of_gt hd)
  filter_upwards [hdiv.eventually hSmall,Filter.eventually_ge_atTop d] with K hsm hKd
  have hj : 1≤K/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hKd)
  have hK : K≤(2*d)*(K/d) := by
    have hb := Nat.lt_mul_div_succ K hd
    nlinarith
  calc
    _ ≤ (((2*d:ℕ):ℝ)*(K/d:ℕ))^3*(1/2:ℝ)^(K/d) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hK
    _ = ((2*d:ℕ):ℝ)^3*((K/d:ℕ)^3*(1/2:ℝ)^(K/d)) := by ring
    _ ≤ _ := hsm

lemma pmf_complement_half {α : Type*} (μ : PMF α) (E : α → Prop)
    (h : (∑' x, if ¬E x then μ x else 0)≤(1/2:ℝ≥0∞)) :
    (1/2:ℝ≥0∞)≤∑' x, if E x then μ x else 0 := by
  have he : (∑' x, if E x then μ x else 0)+(∑' x, if ¬E x then μ x else 0)=1 := by
    rw [← ENNReal.tsum_add]
    convert μ.tsum_coe using 1
    apply tsum_congr
    intro x
    by_cases hx : E x <;> simp [hx]
  have hn : (∑' x, if ¬E x then μ x else 0)≠∞ := ne_of_lt (h.trans_lt (by norm_num))
  calc
    (1/2:ℝ≥0∞)=1-(1/2) := by norm_num
    _ ≤ 1-(∑' x, if ¬E x then μ x else 0) := tsub_le_tsub_left h 1
    _ = _ := by rw [← he,ENNReal.add_sub_cancel_right hn]

theorem acceptedEnvironment_mass (a : ℕ) (ha : 1≤a) :
    ∃ p₀ : ℝ, 0<p₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ, 0≤p → p≤p₀ →
      JointBadLaw μ (ENNReal.ofReal p) → ∀ v w : Vertex,
      (1/2:ℝ≥0∞)≤∑' B, if acceptedEnvironment a B v w then μ B else 0 := by
  let A : ℝ := (2:ℝ)^((2*a+1)^3)
  let D : ℝ := (2:ℝ)^27
  have hA : 0<A := by dsimp [A]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  let p₀ : ℝ := min ((1/432)/D) ((1/2)/A)
  have hp₀ : 0<p₀ := lt_min (div_pos (by norm_num) hD) (div_pos (by norm_num) hA)
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (large_rejection_eventually a ha)
  refine ⟨p₀,hp₀,max M (10*a+3),?_⟩
  intro K hK inst μ p hp hpp hbad v w
  have hKM : M≤K := (le_max_left _ _).trans hK
  have hKd : 10*a+3≤K := (le_max_right _ _).trans hK
  have hK2 : 2<K := by omega
  have hm : 1≤K/(10*a) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hqD : D*p≤1/432 := by
    have h := (le_div_iff₀ hD).mp (hpp.trans (min_le_left _ _))
    nlinarith
  have hqA : A*p≤1/2 := by
    have h := (le_div_iff₀ hA).mp (hpp.trans (min_le_right _ _))
    nlinarith
  have hDeq : ((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p=ENNReal.ofReal (D*p) := by
    rw [ENNReal.ofReal_mul hD.le]
    simp only [D,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  have hAeq : ((2^((2*a+1)^3):ℕ):ℝ≥0∞)*ENNReal.ofReal p=ENNReal.ofReal (A*p) := by
    rw [ENNReal.ofReal_mul hA.le]
    simp only [A,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  have hqDen : ENNReal.ofReal (D*p)≤1/16 := by
    calc
      _ ≤ ENNReal.ofReal (1/16:ℝ) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  have hseries : (∑' m : ℕ, ((2*(m+1)+1)^3:ℕ)*
      (((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p)^(m+1))≤ENNReal.ofReal (1/8:ℝ) := by
    rw [hDeq]
    refine (endpoint_series_le _ hqDen).trans ?_
    calc
      _ = ENNReal.ofReal (54*(D*p)) := by rw [ENNReal.ofReal_mul (p:=54) (q:=D*p) (by norm_num),ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have hlarge : (K:ℝ≥0∞)^3*(((2^((2*a+1)^3):ℕ):ℝ≥0∞)*ENNReal.ofReal p)^(K/(10*a))≤
      ENNReal.ofReal (1/4:ℝ) := by
    rw [hAeq]
    calc
      _ ≤ (K:ℝ≥0∞)^3*(ENNReal.ofReal (1/2:ℝ))^(K/(10*a)) :=
        mul_le_mul' le_rfl (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hqA) _)
      _ = ENNReal.ofReal ((K:ℝ)^3*(1/2:ℝ)^(K/(10*a))) := by
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hM K hKM)
  apply pmf_complement_half μ (fun B ↦ acceptedEnvironment a B v w)
  refine (rejection_probability hK2 ha hm μ _ hbad v w).trans ?_
  refine (add_le_add hlarge (mul_le_mul' le_rfl hseries)).trans_eq ?_
  rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos]

def SimpleGoodPath {K : ℕ} (B : Finset (DiscreteTorus K)) (x y : DiscreteTorus K) :=
  {p : (torusNearestGraph K).Walk x y // p.IsPath ∧ ∀ z∈p.support, z∉B}

lemma exists_nominal_detour {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) (w : PairNoise m) :
    ∃ p : SimpleGoodPath B (torusProjection K v) (torusProjection K (v+![(n:ℤ),Δ₂,Δ₃])),
      ∀ x∈p.val.support,
        x∈(nominalCover (nominalVertices m n v Δ₂ Δ₃ w)).image (torusProjection K) ∨
        shellAttachment R B ((nominalCover (nominalVertices m n v Δ₂ Δ₃ w)).image (torusProjection K)) x := by
  let U := nominalVertices m n v Δ₂ Δ₃ w
  have hi : U 0=v := nominal_initial m n v Δ₂ Δ₃ w
  have hf : U (Fin.last n)=v+![(n:ℤ),Δ₂,Δ₃] := nominal_final m n hn v Δ₂ Δ₃ w
  have hv : v∈nominalCover U := hi ▸ nominal_mem_cover U 0
  have hw : v+![(n:ℤ),Δ₂,Δ₃]∈nominalCover U := hf ▸ nominal_mem_cover U (Fin.last n)
  have hwalk : withinReach nearestStep (↑(nominalCover U)) v (v+![(n:ℤ),Δ₂,Δ₃]) := by
    simpa only [hi,hf] using nominalCover_reach U (nominal_speed m n hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ w)
  obtain ⟨p,hp,hattach⟩ := periodic_good_detour hK R B
    (small_star_of_no_large (by omega) B hB.1) (nominalCover U) hv hw hB.2 hwalk
  exact ⟨⟨p,hp,fun x hx ↦ (hattach x hx).1⟩,fun x hx ↦ (hattach x hx).2⟩

def detourSample {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) (w : PairNoise m) :
    SimpleGoodPath B (torusProjection K v) (torusProjection K (v+![(n:ℤ),Δ₂,Δ₃])) :=
  Classical.choose (exists_nominal_detour hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB w)

lemma detourSample_attachment {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) (w : PairNoise m) :
    ∀ x∈(detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB w).val.support,
      x∈(nominalCover (nominalVertices m n v Δ₂ Δ₃ w)).image (torusProjection K) ∨
      shellAttachment R B ((nominalCover (nominalVertices m n v Δ₂ Δ₃ w)).image (torusProjection K)) x :=
  Classical.choose_spec (exists_nominal_detour hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB w)

def goodPathKernel {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) :
    PMF (SimpleGoodPath B (torusProjection K v) (torusProjection K (v+![(n:ℤ),Δ₂,Δ₃]))) :=
  (pairLaw m).map (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB)

lemma pmf_map_expectation {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    (∑' y, (μ.map f) y*g y)=∑' x, μ x*g (f x) := by
  simp_rw [PMF.map_apply,← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  simp only [ite_mul,zero_mul]
  simp

def pathNoiseTranspose (m : ℕ) : FourNoise m ≃ PairNoise m × PairNoise m where
  toFun w := (firstPathNoise w,secondPathNoise w)
  invFun w := ((w.1.1,w.2.1),(w.1.2,w.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma fourLaw_transpose (m : ℕ) (w : FourNoise m) :
    fourLaw m w=pairLaw m (firstPathNoise w)*pairLaw m (secondPathNoise w) := by
  rcases w with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [fourLaw,pairLaw,firstPathNoise,secondPathNoise,independentPair_apply]
  ring

lemma pair_expectation_transpose (m : ℕ) (f : PairNoise m → PairNoise m → ℝ≥0∞) :
    (∑' x, pairLaw m x*∑' y, pairLaw m y*f x y)=
      ∑' w, fourLaw m w*f (firstPathNoise w) (secondPathNoise w) := by
  simp_rw [← ENNReal.tsum_mul_left,← mul_assoc]
  rw [← ENNReal.tsum_prod]
  have h := (pathNoiseTranspose m).tsum_eq (fun z ↦ pairLaw m z.1*pairLaw m z.2*f z.1 z.2)
  calc
    _ = ∑' w, pairLaw m (firstPathNoise w)*pairLaw m (secondPathNoise w)*f (firstPathNoise w) (secondPathNoise w) := h.symm
    _ = _ := by simp_rw [fourLaw_transpose]

end HardSphere.Lattice

end

end OAI
