import OAI.Analysis.FreeEntropy.TensorConcat

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

def labelSpace (P : Word B N G → Prop) : Submodule ℂ (Space B N G) :=
  Submodule.span ℂ {x | ∃ w, P w ∧ x = basis w}

omit [Group G] in
theorem basis_mem_labelSpace [Group G] {P : Word B N G → Prop} {w : Word B N G} (hw : P w) :
    basis w ∈ labelSpace P := Submodule.subset_span ⟨w, hw, rfl⟩

omit [Group G] in
theorem labelSpace_action [Group G] {P Q : Word B N G → Prop} {T : Space B N G →L[ℂ] Space B N G}
    (hT : ∀ w, P w → T (basis w) ∈ labelSpace Q) {x : Space B N G}
    (hx : x ∈ labelSpace P) : T x ∈ labelSpace Q := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,hw,rfl⟩ := hx; exact hT w hw
  | zero => simp
  | add x y _ _ hx hy => simpa using (labelSpace Q).add_mem hx hy
  | smul z x _ hx => simpa using (labelSpace Q).smul_mem z hx

 theorem centered_labelSpace_suffix {P Q : Word B N G → Prop}
    {x : Space B N G} (hx : x ∈ labelSpace P) (v : Word B N G)
    (hPQ : ∀ w, P w → w ≠ empty → Q (concat w v)) :
    suffixEmbedding v (x - x empty • basis empty) ∈ labelSpace Q := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    by_cases he : w = empty
    · subst w
      simp [basis, lp.single_apply]
    · have hz : (basis w : Space B N G) empty = 0 := by
        simp [basis, lp.single_apply, Ne.symm he]
      rw [hz, zero_smul, sub_zero, suffixEmbedding_basis]
      exact basis_mem_labelSpace (hPQ w hw he)
  | zero => simp
  | add x y _ _ hx hy =>
    have h : (x + y) - (x + y) empty • basis empty =
        (x - x empty • basis empty) + (y - y empty • basis empty) := by
      change (x + y) - (x empty + y empty) • basis empty = _
      rw [add_smul]; abel
    rw [h, map_add]
    exact (labelSpace Q).add_mem hx hy
  | smul z x _ hx =>
    have h : z • x - (z • x) empty • basis empty =
        z • (x - x empty • basis empty) := by
      change z • x - (z * x empty) • basis empty = _
      rw [smul_sub, smul_smul]
    rw [h, map_smul]
    exact (labelSpace Q).smul_mem z hx

 theorem labelSpace_vacuum_zero {P : Word B N G → Prop} (hP : ¬ P empty)
    {x : Space B N G} (hx : x ∈ labelSpace P) : x empty = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    have hne : empty ≠ w := fun h => hP (h ▸ hw)
    simp [basis, lp.single_apply, hne]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul z x _ hx => simp [hx]

 theorem trace_eq_vacuum_coefficient (T : Space B N G →L[ℂ] Space B N G) :
    trace (tracialVector B N G) T = (T (basis empty)) empty := by
  simp [trace, tracialVector, basis, lp.inner_single_left]

 theorem annihilationB_preserves_supported {J : Set N} {w : Word B N G}
    (hw : Supported J w) (b : B) :
    star (creationB b) (basis w) ∈ labelSpace (Supported J) := by
  rw [basis, annihilationB_single]
  cases h : removeB b w with
  | none => exact (labelSpace _).zero_mem
  | some v =>
    have hv := (removeB_spec b v w).mp h
    subst w
    exact basis_mem_labelSpace hw

 theorem annihilationN_preserves_supported {J : Set N} {w : Word B N G}
    (hw : Supported J w) (i : N) :
    star (creationN i) (basis w) ∈ labelSpace (Supported J) := by
  rw [basis, annihilationN_single]
  cases h : removeN i w with
  | none => exact (labelSpace _).zero_mem
  | some v =>
    have hv := (removeN_spec i v w).mp h
    subst w
    apply basis_mem_labelSpace
    intro p hp
    exact hw p (List.mem_cons_of_mem _ hp)

 theorem background_preserves_supported {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    ∀ x ∈ labelSpace (Supported J), T x ∈ labelSpace (Supported J) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,hi,rfl⟩)
    · apply labelSpace_action
      intro w hw
      change creationB b (basis w) + star (creationB b) (basis w) ∈ _
      apply Submodule.add_mem
      · simpa [basis] using basis_mem_labelSpace (supported_leftB hw b)
      · exact annihilationB_preserves_supported hw b
    · apply labelSpace_action
      intro w hw
      simpa [basis] using basis_mem_labelSpace (supported_leftG hw g)
    · apply labelSpace_action
      intro w hw
      change creationN i (basis w) + star (creationN i) (basis w) ∈ _
      apply Submodule.add_mem
      · simpa [basis] using basis_mem_labelSpace (supported_leftN hw hi)
      · exact annihilationN_preserves_supported hw i
  | algebraMap z =>
    intro x hx
    simpa using (labelSpace (Supported J)).smul_mem z hx
  | add T U _ _ hT hU =>
    intro x hx
    exact Submodule.add_mem _ (hT x hx) (hU x hx)
  | mul T U _ _ hT hU =>
    intro x hx
    exact hT (U x) (hU x hx)

omit [DecidableEq N] [DecidableEq G] in
theorem removeB_concat_noise [DecidableEq N] [DecidableEq G] (b : B) (w v : Word B N G) (i : N) :
    removeB b (concat w (leftN i v)) = (removeB b w).map (fun u => concat u (leftN i v)) := by
  rcases w with ⟨⟨l,g⟩,t⟩
  cases t with
  | nil =>
    cases l with
    | nil => simp [concat, concatAux, atomMul, leftN, push, removeB]
    | cons c l =>
      by_cases h : b = c <;> simp [concat, concatAux, atomMul, leftN, push, removeB, h]
  | cons p t =>
    rcases p with ⟨j,a⟩
    cases l with
    | nil => rfl
    | cons c l =>
      by_cases h : b = c <;> simp [concat, concatAux, leftN, push, removeB, h]

 theorem removeN_concat_noise (i k : N) (hik : i ≠ k) (w v : Word B N G) :
    removeN i (concat w (leftN k v)) = (removeN i w).map (fun u => concat u (leftN k v)) := by
  rcases w with ⟨a,t⟩
  cases t with
  | nil =>
    by_cases ha : a = ([],1)
    · subst a
      simp [concat, concatAux, atomMul, leftN, push, removeN, hik]
    · have ham : atomMul a ([],1) = a := by simp [atomMul]
      simp [concat, concatAux, leftN, push, removeN, ha, ham]
  | cons p t =>
    rcases p with ⟨j,a'⟩
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [concat, concatAux, leftN, push, removeN, ha, hij]

 theorem annihilationB_suffix_noise (b : B) (i : N) (v : Word B N G) :
    Commute (star (creationB b)) (suffixEmbedding (leftN i v)) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (creationB b) (suffixEmbedding (leftN i v) (lp.single 2 w z)) =
    suffixEmbedding (leftN i v) (star (creationB b) (lp.single 2 w z))
  rw [suffixEmbedding_single, annihilationB_single, annihilationB_single, removeB_concat_noise]
  cases removeB b w <;> simp

 theorem annihilationN_suffix_noise (i k : N) (hik : i ≠ k) (v : Word B N G) :
    Commute (star (creationN i)) (suffixEmbedding (leftN k v)) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (creationN i) (suffixEmbedding (leftN k v) (lp.single 2 w z)) =
    suffixEmbedding (leftN k v) (star (creationN i) (lp.single 2 w z))
  rw [suffixEmbedding_single, annihilationN_single, annihilationN_single,
    removeN_concat_noise i k hik]
  cases removeN i w <;> simp

 theorem background_commutes_suffix {J : Set N} {k : N} (hk : k ∉ J) (v : Word B N G)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute T (suffixEmbedding (leftN k v)) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,hi,rfl⟩)
    · exact (creationB_suffix b _).add_left (annihilationB_suffix_noise b k v)
    · exact unitaryG_suffix g _
    · exact (creationN_suffix i _).add_left
        (annihilationN_suffix_noise i k (fun h => hk (h ▸ hi)) v)
  | algebraMap z => exact Algebra.commute_algebraMap_left z _
  | add T U _ _ hT hU => exact hT.add_left hU
  | mul T U _ _ hT hU => exact hT.mul_left hU

 theorem centered_background_basis {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J)
    (hcenter : trace (tracialVector B N G) T = 0) {k : N} (hk : k ∉ J)
    {v : Word B N G} (hv : StartsNoise k v) :
    T (basis v) ∈ labelSpace (StartsBackground J) := by
  obtain ⟨v,rfl⟩ := hv
  have hc := congrArg (fun A : Space B N G →L[ℂ] Space B N G => A (basis empty))
    (background_commutes_suffix hk v hT).eq
  simp only [mul_apply_eq_comp, suffixEmbedding_basis, concat_empty_left] at hc
  have hx := background_preserves_supported hT (basis empty)
    (basis_mem_labelSpace (supported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix hx (leftN k v)
    (fun w hw hne => startsBackground_concat (supported_ne_empty_starts hw hne) ⟨v,rfl⟩)
  simpa only [hz, zero_smul, sub_zero, ← hc] using hs

def PureSupported (J : Set N) (w : Word B N G) : Prop :=
  ∃ l : List N, (∀ i ∈ l, i ∈ J) ∧ w = noiseWord l

def StartsNoiseIn (J : Set N) (w : Word B N G) : Prop :=
  ∃ i ∈ J, StartsNoise i w

 theorem removeN_none_iff (i : N) (w : Word B N G) :
    removeN i w = none ↔ ¬ StartsNoise i w := by
  constructor
  · intro h ⟨v,hv⟩
    have hv' := (removeN_spec i v w).mpr hv.symm
    rw [h] at hv'
    contradiction
  · intro h
    cases he : removeN i w with
    | none => rfl
    | some v => exact False.elim (h ⟨v, ((removeN_spec i v w).mp he).symm⟩)

 theorem semicircularN_basis_leftN (i j : N) (w : Word B N G) :
    semicircularN i (basis (leftN j w)) =
      basis (leftN i (leftN j w)) + if i = j then basis w else 0 := by
  by_cases h : i = j <;> simp [semicircularN, basis, annihilationN_single, removeN, leftN, push, h]

 theorem semicircularN_basis_not_starts (i : N) (w : Word B N G)
    (hw : ¬ StartsNoise i w) :
    semicircularN i (basis w) = basis (leftN i w) := by
  simp [semicircularN, basis, annihilationN_single, (removeN_none_iff i w).mpr hw]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem pureSupported_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (J : Set N) : PureSupported J (empty : Word B N G) :=
  ⟨[], by simp, rfl⟩

 theorem semicircularN_preserves_pureSupported {J : Set N} {i : N} (hi : i ∈ J)
    {x : Space B N G} (hx : x ∈ labelSpace (PureSupported J)) :
    semicircularN i x ∈ labelSpace (PureSupported J) := by
  apply labelSpace_action (x := x) _ hx
  rintro w ⟨l,hl,rfl⟩
  cases l with
  | nil =>
    have hn : ¬ StartsNoise i (empty : Word B N G) := by
      rintro ⟨v,hv⟩
      simp [empty, leftN, push] at hv
    rw [noiseWord_nil, semicircularN_basis_not_starts i empty hn]
    exact basis_mem_labelSpace ⟨[i], by simpa using hi, rfl⟩
  | cons j l =>
    rw [noiseWord_cons, semicircularN_basis_leftN]
    apply Submodule.add_mem
    · exact basis_mem_labelSpace ⟨i :: j :: l, by simpa using And.intro hi hl, rfl⟩
    · split_ifs
      · exact basis_mem_labelSpace ⟨l, fun k hk => hl k (List.mem_cons_of_mem _ hk), rfl⟩
      · exact Submodule.zero_mem _

 theorem semicircularN_pureSuffix {J : Set N} {i : N} (hi : i ∈ J)
    (v : Word B N G) (hv : ∀ j ∈ J, ¬ StartsNoise j v)
    {x : Space B N G} (hx : x ∈ labelSpace (PureSupported J)) :
    semicircularN i (suffixEmbedding v x) = suffixEmbedding v (semicircularN i x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,⟨l,hl,rfl⟩,rfl⟩ := hx
    cases l with
    | nil =>
      rw [noiseWord_nil, suffixEmbedding_basis, concat_empty_left,
        semicircularN_basis_not_starts i v (hv i hi)]
      have hn : ¬ StartsNoise i (empty : Word B N G) := by
        rintro ⟨w,hw⟩
        simp [empty, leftN, push] at hw
      rw [semicircularN_basis_not_starts i empty hn, suffixEmbedding_basis]
      rw [← leftN_concat, concat_empty_left]
    | cons j l =>
      rw [noiseWord_cons, suffixEmbedding_basis, ← leftN_concat,
        semicircularN_basis_leftN, semicircularN_basis_leftN, map_add]
      by_cases h : i = j <;> simp [h, suffixEmbedding_basis, ← leftN_concat]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul z x _ hx => simp [hx]

 theorem noise_adjoin_suffix {J : Set N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ (semicircularN '' J)) (v : Word B N G)
    (hv : ∀ j ∈ J, ¬ StartsNoise j v) :
    ∀ x ∈ labelSpace (PureSupported J), T x ∈ labelSpace (PureSupported J) ∧
      T (suffixEmbedding v x) = suffixEmbedding v (T x) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨i,hi,rfl⟩ := hT
    exact fun x hx => ⟨semicircularN_preserves_pureSupported hi hx,
      semicircularN_pureSuffix hi v hv hx⟩
  | algebraMap z =>
    intro x hx
    exact ⟨by simpa using (labelSpace (PureSupported J)).smul_mem z hx, by simp⟩
  | add T U _ _ hT hU =>
    intro x hx
    exact ⟨Submodule.add_mem _ (hT x hx).1 (hU x hx).1,
      by simp only [add_apply, (hT x hx).2, (hU x hx).2, map_add]⟩
  | mul T U _ _ hT hU =>
    intro x hx
    exact ⟨(hT (U x) (hU x hx).1).1,
      by simp only [mul_apply_eq_comp, (hU x hx).2, (hT (U x) (hU x hx).1).2]⟩

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem pureSupported_ne_empty_concat [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : PureSupported J w) (hne : w ≠ empty) (v : Word B N G) :
    StartsNoiseIn J (concat w v) := by
  obtain ⟨l,hl,rfl⟩ := hw
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons i l => exact ⟨i, hl i (by simp), concat (noiseWord l) v, rfl⟩

 theorem centered_noise_basis {J : Set N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ (semicircularN '' J))
    (hc : trace (tracialVector B N G) T = 0) (v : Word B N G)
    (hv : ∀ j ∈ J, ¬ StartsNoise j v) :
    T (basis v) ∈ labelSpace (StartsNoiseIn J) := by
  have h := noise_adjoin_suffix hT v hv (basis empty)
    (basis_mem_labelSpace (pureSupported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix h.1 v
    (fun w hw hne => pureSupported_ne_empty_concat hw hne v)
  simpa only [hz, zero_smul, sub_zero, ← h.2, suffixEmbedding_basis,
    concat_empty_left] using hs

 theorem centered_coordinate_basis {i : N} {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ Algebra.adjoin ℂ {semicircularN i})
    (hc : trace (tracialVector B N G) T = 0) (v : Word B N G) (hv : ¬ StartsNoise i v) :
    T (basis v) ∈ labelSpace (StartsNoise i) := by
  have hT' : T ∈ Algebra.adjoin ℂ (semicircularN '' {i}) := by simpa using hT
  have h := centered_noise_basis hT' hc v (by simpa using hv)
  have he : StartsNoiseIn ({i} : Set N) = (StartsNoise i : Word B N G → Prop) := by
    funext w
    simp [StartsNoiseIn]
  rwa [he] at h

 theorem centered_background_vacuum {J : Set N}
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J)
    (hc : trace (tracialVector B N G) T = 0) :
    T (basis empty) ∈ labelSpace (StartsBackground J) := by
  have hx := background_preserves_supported hT (basis empty)
    (basis_mem_labelSpace (supported_empty J))
  have hz : (T (basis empty)) empty = 0 := by rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_labelSpace_suffix hx empty
    (fun w hw hne => by simpa using supported_ne_empty_starts hw hne)
  have hid : suffixEmbedding (empty : Word B N G) = 1 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro w
    apply ContinuousLinearMap.ext
    intro z
    simp
  simpa only [hz, zero_smul, sub_zero, hid, one_apply_eq_self] using hs

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsNoise_injective [DecidableEq B] [DecidableEq N] [DecidableEq G] {i j : N} {w : Word B N G}
    (hi : StartsNoise i w) (hj : StartsNoise j w) : i = j := by
  obtain ⟨v,rfl⟩ := hi
  obtain ⟨u,hu⟩ := hj
  have h := congrArg (fun w : Word B N G => w.2.head?.map Prod.fst) hu
  simpa [leftN, push] using h

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem not_startsNoise_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (i : N) : ¬ StartsNoise i (empty : Word B N G) := by
  rintro ⟨v,hv⟩
  simp [empty, leftN, push] at hv

 theorem not_startsBackground_empty (J : Set N) : ¬ StartsBackground J (empty : Word B N G) := by
  rintro (h | ⟨i,_,hi⟩)
  · exact h rfl
  · exact not_startsNoise_empty i hi

def noiseAlgebras {κ : Type} (J : Set N) (σ : κ → N) :
    Option κ → Subalgebra ℂ (Space B N G →L[ℂ] Space B N G)
  | none => backgroundAlgebra J
  | some i => Algebra.adjoin ℂ {semicircularN (σ i)}

def StartsColor {κ : Type} (J : Set N) (σ : κ → N) : Option κ → Word B N G → Prop
  | none => StartsBackground J
  | some i => StartsNoise (σ i)

 theorem centered_noiseAlgebras_vacuum {κ : Type} (J : Set N) (σ : κ → N)
    (i : Option κ) {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ noiseAlgebras J σ i) (hc : trace (tracialVector B N G) T = 0) :
    T (basis empty) ∈ labelSpace (StartsColor J σ i) := by
  cases i with
  | none => exact centered_background_vacuum hT hc
  | some i => exact centered_coordinate_basis hT hc empty (not_startsNoise_empty _)

 theorem centered_noiseAlgebras_starts {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    {i j : Option κ} (hij : i ≠ j) {T : Space B N G →L[ℂ] Space B N G}
    (hT : T ∈ noiseAlgebras J σ i) (hc : trace (tracialVector B N G) T = 0)
    {x : Space B N G} (hx : x ∈ labelSpace (StartsColor J σ j)) :
    T x ∈ labelSpace (StartsColor J σ i) := by
  apply labelSpace_action (x := x) _ hx
  intro w hw
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some j => exact centered_background_basis hT hc (hs j) hw
  | some i =>
    apply centered_coordinate_basis hT hc
    cases j with
    | none => exact startsBackground_not_noise hw (hs i)
    | some j =>
      intro hi
      exact hij (congrArg some (hσ (startsNoise_injective hi hw)))

 theorem alternating_noise_product_starts {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    ∀ (k : ℕ) (hk : 0 < k) (j : Fin k → Option κ)
      (a : Fin k → Space B N G →L[ℂ] Space B N G),
      (∀ r, a r ∈ noiseAlgebras J σ (j r)) →
      (∀ r, trace (tracialVector B N G) (a r) = 0) →
      (∀ (r : ℕ) (hr : r + 1 < k),
        j ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ ≠ j ⟨r + 1, hr⟩) →
      (List.ofFn a).prod (basis empty) ∈ labelSpace (StartsColor J σ (j ⟨0,hk⟩)) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk j a ha hc hadj
    rw [List.ofFn_succ, List.prod_cons, mul_apply_eq_comp]
    cases k with
    | zero => exact centered_noiseAlgebras_vacuum J σ (j 0) (ha 0) (hc 0)
    | succ k =>
      have ht := ih (by omega) (fun r => j r.succ) (fun r => a r.succ)
        (fun r => ha r.succ) (fun r => hc r.succ) (by
          intro r hr
          exact hadj (r+1) (by omega))
      exact centered_noiseAlgebras_starts J σ hσ hs (hadj 0 (by omega)) (ha 0) (hc 0) ht

theorem free_noiseAlgebras {κ : Type} (J : Set N) (σ : κ → N)
    (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    FreeSubalgebras (tracialVector B N G) (noiseAlgebras J σ) := by
  intro k hk j a ha hc hadj
  rw [trace_eq_vacuum_coefficient]
  apply labelSpace_vacuum_zero _ (alternating_noise_product_starts J σ hσ hs k hk j a ha hc hadj)
  cases j ⟨0,hk⟩ with
  | none => exact not_startsBackground_empty J
  | some i => exact not_startsNoise_empty (σ i)

theorem freeStandardNoise {m n : ℕ} (J : Set (Fin m))
    (X : Fin n → Space B (Fin m) G →L[ℂ] Space B (Fin m) G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → Fin m) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    FreeStandardNoise (tracialVector B (Fin m) G) X (fun i => semicircularN (σ i)) := by
  refine ⟨fun i k => trace_semicircularN_pow (σ i) k, ?_⟩
  apply (free_noiseAlgebras J σ hσ hs).mono
  intro j
  cases j with
  | none =>
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact hX i
  | some i => exact le_rfl

end FreeTensor
end FiniteEntropySeparation

end

end OAI
