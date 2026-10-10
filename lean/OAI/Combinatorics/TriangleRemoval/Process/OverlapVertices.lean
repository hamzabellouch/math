import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Process.TriangleLiftCount

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical

namespace SharpTerminalLeave

def overlapVertices {k n : ℕ} (W : Finset (Fin n)) (φ : Fin k ↪ Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun v => φ v ∈ W)

@[simp] lemma mem_overlapVertices {k n : ℕ} (W : Finset (Fin n)) (φ : Fin k ↪ Fin n) (v : Fin k) :
    v ∈ overlapVertices W φ ↔ φ v ∈ W := by simp [overlapVertices]

lemma overlapVertices_contains_roots {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n))
    (hW : ∀ v, ψ v ∈ W) (φ : RootedInjection T ψ) :
    T.roots ⊆ overlapVertices W φ.val := by
  intro v hv
  rw [mem_overlapVertices,φ.property ⟨v,hv⟩]
  exact hW ⟨v,hv⟩

theorem rooted_overlap_fiber_card {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n)) (J : Finset (Fin k)) :
    Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} ≤
      W.card^J.card * n^(k-J.card) := by
  let encode : {φ : RootedInjection T ψ // overlapVertices W φ.val = J} →
      (J → W) × ({v : Fin k // v ∉ J} → Fin n) := fun φ =>
        (fun v => ⟨φ.val.val v, by
          have hv : v.val ∈ overlapVertices W φ.val.val := by rw [φ.property]; exact v.property
          exact (mem_overlapVertices W φ.val.val v).mp hv⟩,
         fun v => φ.val.val v)
  have hinj : Function.Injective encode := by
    intro φ χ he
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    by_cases hv : v ∈ J
    · exact congrArg Subtype.val (congrFun (congrArg Prod.fst he) ⟨v,hv⟩)
    · exact congrFun (congrArg Prod.snd he) ⟨v,hv⟩
  have hc := Fintype.card_le_of_injective encode hinj
  have hfree : Fintype.card {v : Fin k // v ∉ J} = k-J.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      Fintype.card_subtype_compl (fun v : Fin k => v ∈ J)
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin,hfree] using hc

lemma imageEdges_inter_subset_induced {k n : ℕ} (T : RootedTemplate k)
    (φ : Fin k ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hF : ∀ e ∈ F, e ⊆ W) :
    F ∩ imageEdges T φ ⊆
      (T.edges.filter (fun e => e ⊆ overlapVertices W φ)).image (fun e => e.map φ) := by
  intro e he
  obtain ⟨heF,heT⟩ := Finset.mem_inter.mp he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp heT
  apply Finset.mem_image.mpr
  refine ⟨f,Finset.mem_filter.mpr ⟨hf,?_⟩,rfl⟩
  intro v hv
  rw [mem_overlapVertices]
  exact hF (f.map φ) heF (Finset.mem_map.mpr ⟨v,hv,rfl⟩)

theorem rooted_new_edges_lower {k n : ℕ} (T : RootedTemplate k)
    (φ : Fin k ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hF : ∀ e ∈ F, e ⊆ W) :
    T.edges.card-(T.edges.filter (fun e => e ⊆ overlapVertices W φ)).card ≤
      (imageEdges T φ \ F).card := by
  have hc := Finset.card_le_card (imageEdges_inter_subset_induced T φ W F hF)
  have hm : ((T.edges.filter (fun e => e ⊆ overlapVertices W φ)).image (fun e => e.map φ)).card =
      (T.edges.filter (fun e => e ⊆ overlapVertices W φ)).card := by
    apply Finset.card_image_of_injective
    exact fun _ _ h => Finset.map_injective φ h
  rw [hm] at hc
  rw [Finset.card_sdiff,imageEdges_card]
  omega

theorem rooted_weighted_extension_bound {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (W : Finset (Fin n)) (F : Graph n)
    (hW : ∀ v, ψ v ∈ W) (hF : ∀ e ∈ F, e ⊆ W)
    {p M : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M) :
    (∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) ≤
      (2*((W.card : ℝ)+1))^k*M := by
  let b : Finset (Fin k) → ℕ := fun J => T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card
  have hfirst : (∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) ≤
      ∑ φ : RootedInjection T ψ, p^(b (overlapVertices W φ.val)) := by
    apply Finset.sum_le_sum
    intro φ _
    exact pow_le_pow_of_le_one hp hp1 (rooted_new_edges_lower T φ.val W F hF)
  have hgroup : (∑ φ : RootedInjection T ψ, p^(b (overlapVertices W φ.val))) =
      ∑ J : Finset (Fin k),
        (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ)*p^(b J) := by
    rw [← Fintype.sum_fiberwise (fun φ : RootedInjection T ψ => overlapVertices W φ.val)]
    apply Finset.sum_congr rfl
    intro J _
    calc
      _ = ∑ _φ : {φ : RootedInjection T ψ // overlapVertices W φ.val = J}, p^(b J) := by
        apply Finset.sum_congr rfl
        intro φ _
        rw [φ.property]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hfiber (J : Finset (Fin k)) :
      (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ)*p^(b J) ≤
        ((W.card : ℝ)+1)^k*M := by
    by_cases hJ : T.roots ⊆ J
    · have hjk : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
      have hc : (Fintype.card {φ : RootedInjection T ψ // overlapVertices W φ.val = J} : ℝ) ≤
          (W.card : ℝ)^J.card*(n : ℝ)^(k-J.card) := by
        exact_mod_cast rooted_overlap_fiber_card T ψ W J
      have hw : (W.card : ℝ)^J.card ≤ ((W.card : ℝ)+1)^k := by
        calc
          _ ≤ ((W.card : ℝ)+1)^J.card := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
          _ ≤ _ := pow_le_pow_right₀ (show (1 : ℝ) ≤ (W.card : ℝ)+1 by have hz : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _; linarith) hjk
      calc
        _ ≤ ((W.card : ℝ)^J.card*(n : ℝ)^(k-J.card))*p^(b J) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hp _)
        _ = (W.card : ℝ)^J.card*((n : ℝ)^(k-J.card)*p^(b J)) := by ring
        _ ≤ ((W.card : ℝ)+1)^k*M :=
          mul_le_mul hw (hscale J hJ) (by positivity) (by positivity)
    · have he : IsEmpty {φ : RootedInjection T ψ // overlapVertices W φ.val = J} := by
        refine ⟨fun φ => hJ ?_⟩
        rw [← φ.property]
        exact overlapVertices_contains_roots T ψ W hW φ.val
      have := he
      simp only [Fintype.card_of_isEmpty,Nat.cast_zero,zero_mul]
      positivity
  calc
    _ ≤ _ := hfirst
    _ = _ := hgroup
    _ ≤ ∑ _J : Finset (Fin k), ((W.card : ℝ)+1)^k*M := Finset.sum_le_sum (fun J _ => hfiber J)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,
      Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,nsmul_eq_mul]; rw [mul_pow]; ring

lemma rooted_completion_factorization {k n : ℕ} (T : RootedTemplate k)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) (p : ℝ) :
    ((n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (fun e => e ⊆ J)).card) *
      ((n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card)) =
        rootedScaling T n p := by
  have hi := Finset.card_le_card hJ
  have hj : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
  have he := Finset.card_le_card (Finset.filter_subset (fun e => e ⊆ J) T.edges)
  unfold rootedScaling
  calc
    _ = (n : ℝ)^((J.card-T.roots.card)+(k-J.card))*
        p^((T.edges.filter (fun e => e ⊆ J)).card+
          (T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card)) := by rw [pow_add,pow_add]; ring
    _ = _ := by congr 2 <;> omega

theorem largeTemplate_completion_scale {k n : ℕ} (T : RootedTemplate k)
    {p : ℝ} (hp : 0 ≤ p) (hT : largeTemplateEligible T n p)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤
      rootedScaling T n p := by
  have hJscale := hT J hJ (T.edges.filter (fun e => e ⊆ J))
    (Finset.filter_subset _ _) (fun e he => (Finset.mem_filter.mp he).2)
  rw [← rooted_completion_factorization T J hJ p]
  exact le_mul_of_one_le_left (by positivity) hJscale

def copyUnionSum {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) : ℕ → (Graph n → ℝ) → Graph n → ℝ
  | 0,f,F => f F
  | q+1,f,F => ∑ a, copyUnionSum required q f (F ∪ required a)

lemma copyUnionSum_const_mul {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (q : ℕ) (f : Graph n → ℝ) (c : ℝ) (F : Graph n) :
    copyUnionSum required q (fun J => c*f J) F = c*copyUnionSum required q f F := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih => simp only [copyUnionSum,ih,Finset.mul_sum]

lemma copyUnionSum_mono_bounded {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (b N q : ℕ) (hsize : ∀ a, (required a).card ≤ b)
    (f g : Graph n → ℝ) (hfg : ∀ F, F.card ≤ N → f F ≤ g F)
    (F : Graph n) (hF : F.card+q*b ≤ N) :
    copyUnionSum required q f F ≤ copyUnionSum required q g F := by
  induction q generalizing F with
  | zero => exact hfg F (by simpa using hF)
  | succ q ih =>
    apply Finset.sum_le_sum
    intro a _
    apply ih
    have hc := Finset.card_union_le F (required a)
    have hs := hsize a
    have hm : (q+1)*b = q*b+b := by ring
    omega

lemma copyUnionSum_intact {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (q : ℕ) (G F : Graph n) :
    copyUnionSum required q (fun J => intact J G) F = intact F G*(copyCount required G)^q := by
  induction q generalizing F with
  | zero => simp [copyUnionSum]
  | succ q ih =>
    simp only [copyUnionSum,ih,intact_union]
    rw [← Finset.sum_mul,← Finset.mul_sum]
    change (intact F G*copyCount required G)*(copyCount required G)^q = _
    rw [pow_succ']
    ring

lemma copyUnionSum_mean {n : ℕ} {α Ω : Type*} [Fintype α] [Fintype Ω]
    (required : α → Graph n) (q : ℕ) (μ : PMF Ω) (f : Graph n → Ω → ℝ) (F : Graph n) :
    copyUnionSum required q (fun J => pmfMean μ (f J)) F =
      pmfMean μ (fun ω => copyUnionSum required q (fun J => f J ω) F) := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    simp only [copyUnionSum,ih]
    exact (pmfMean_sum μ _).symm

lemma rooted_image_vertices {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n)
    {e : Finset (Fin n)} (he : e ∈ imageEdges T φ) : e ⊆ Finset.univ.map φ := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact Finset.map_subset_map.mpr (Finset.subset_univ f)

theorem rooted_union_moment_partition {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) {p M : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M)
    (N q : ℕ) (W : Finset (Fin n)) (F : Graph n)
    (hW : ∀ v, ψ v ∈ W) (hF : ∀ e ∈ F, e ⊆ W) (hcap : W.card+q*k ≤ N) :
    copyUnionSum (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      q (fun J => p^J.card) F ≤
      ((2*((N : ℝ)+1))^k*M)^q*p^F.card := by
  let B : ℝ := (2*((N : ℝ)+1))^k*M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change _ ≤ B^q*p^F.card
  induction q generalizing W F with
  | zero => simp [copyUnionSum]
  | succ q ih =>
    have hWcap : W.card ≤ N := by omega
    have hWreal : (W.card : ℝ) ≤ N := by exact_mod_cast hWcap
    have hb : (2*((W.card : ℝ)+1))^k*M ≤ B := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hext := (rooted_weighted_extension_bound T ψ W F hW hF hp hp1 hM hscale).trans hb
    calc
      _ ≤ ∑ φ : RootedInjection T ψ, B^q*p^(F ∪ imageEdges T φ.val).card := by
        apply Finset.sum_le_sum
        intro φ _
        apply ih (W := W ∪ Finset.univ.map φ.val)
        · intro v
          exact Finset.mem_union_left _ (hW v)
        · intro e he
          rcases Finset.mem_union.mp he with he | he
          · exact (hF e he).trans Finset.subset_union_left
          · exact (rooted_image_vertices T φ.val he).trans Finset.subset_union_right
        · have hc := Finset.card_union_le W (Finset.univ.map φ.val)
          have hm : (Finset.univ.map φ.val).card = k := by simp
          have hq : (q+1)*k = q*k+k := by ring
          omega
      _ = B^q*p^F.card*(∑ φ : RootedInjection T ψ, p^(imageEdges T φ.val \ F).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro φ _
        have hc : (F ∪ imageEdges T φ.val).card = F.card+(imageEdges T φ.val \ F).card := by
          have hu := Finset.card_union_add_card_inter F (imageEdges T φ.val)
          have hs := Finset.card_sdiff (s := F) (t := imageEdges T φ.val)
          have hl := Finset.card_le_card (Finset.inter_subset_right : F ∩ imageEdges T φ.val ⊆ imageEdges T φ.val)
          omega
        rw [hc,pow_add]
        ring
      _ ≤ B^q*p^F.card*B := mul_le_mul_of_nonneg_left hext (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem rooted_count_moment_from_survival {k n : ℕ} {Ω : Type*} [Fintype Ω]
    (T : RootedTemplate k) (ψ : {v // v ∈ T.roots} ↪ Fin n)
    (μ : PMF Ω) (state : Ω → Graph n) (A : Ω → Prop)
    (q : ℕ) {p M U : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hscale : ∀ J : Finset (Fin k), T.roots ⊆ J →
      (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤ M)
    (hsurvive : ∀ F : Graph n, F.card ≤ q*T.edges.card →
      pmfMean μ (fun ω => if A ω then intact F (state ω) else 0) ≤ U*p^F.card) :
    pmfMean μ (fun ω => if A ω then (rootedCount T ψ (state ω))^q else 0) ≤
      U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k*M)^q := by
  let req : RootedInjection T ψ → Graph n := fun φ => imageEdges T φ.val
  let f : Graph n → ℝ := fun F => pmfMean μ (fun ω => if A ω then intact F (state ω) else 0)
  have he : copyUnionSum req q f ∅ =
      pmfMean μ (fun ω => if A ω then (rootedCount T ψ (state ω))^q else 0) := by
    rw [copyUnionSum_mean req q μ]
    apply pmfMean_congr
    intro ω _
    by_cases hA : A ω
    · simp only [hA,ite_true]
      rw [copyUnionSum_intact]
      simp only [intact,Finset.empty_subset,ite_true,one_mul]
      rfl
    · simp only [hA,ite_false]
      have hz := copyUnionSum_const_mul req q (fun _ => (1 : ℝ)) 0 ∅
      simpa only [zero_mul] using hz
  let W : Finset (Fin n) := Finset.univ.map ψ
  have hw : ∀ v, ψ v ∈ W := fun v => Finset.mem_map.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hWcard : W.card ≤ k := by
    have he : W.card = T.roots.card := by simp [W]
    rw [he]
    simpa only [Fintype.card_fin] using T.roots.card_le_univ
  have hb := rooted_union_moment_partition T ψ hp hp1 hM hscale ((q+1)*k) q W ∅ hw
    (by simp) (by nlinarith)
  simp only [Finset.card_empty,pow_zero,mul_one] at hb
  calc
    _ = copyUnionSum req q f ∅ := he.symm
    _ ≤ copyUnionSum req q (fun F => U*p^F.card) ∅ :=
      copyUnionSum_mono_bounded req T.edges.card (q*T.edges.card) q
        (fun φ => by simp only [req,imageEdges_card,le_refl]) f _ hsurvive ∅ (by simp)
    _ = U*copyUnionSum req q (fun F => p^F.card) ∅ := copyUnionSum_const_mul req q _ U ∅
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hU

theorem pmfMean_stopped_power_tail {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (A : Ω → Prop) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (q : ℕ) {t B : ℝ} (ht : 0 < t)
    (hmean : pmfMean μ (fun ω => if A ω then X ω^q else 0) ≤ B) :
    pmfMean μ (fun ω => if A ω ∧ t ≤ X ω then 1 else 0) ≤ B/t^q := by
  apply (le_div_iff₀ (pow_pos ht q)).mpr
  rw [← pmfMean_mul_const]
  apply le_trans _ hmean
  apply pmfMean_mono
  intro ω _
  by_cases hA : A ω
  · by_cases htX : t ≤ X ω
    · simp only [hA,htX,and_self,ite_true,one_mul]
      exact pow_le_pow_left₀ ht.le htX q
    · simp only [hA,htX,and_false,ite_false,ite_true,zero_mul]
      exact pow_nonneg (hX ω) q
  · simp [hA]

end SharpTerminalLeave
end
end

end OAI
