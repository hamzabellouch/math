import OAI.Analysis.C0Absorption.Selection

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem tsupport_product_subset_right {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport g := by
  simpa only [mul_comm] using tsupport_product_subset_left g f

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_mul_tail {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) (a N : ℕ) :
    (fun s => f s*tailFactor (dyadic a) (N+1) s.val) ∈ VClass B (h+a+1) := by
  obtain ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩ := hf
  let t : TailOperation := ⟨a,N,true⟩
  refine ⟨γ,r,t::ts,by omega,by omega,by simpa using (show ts.length+1 ≤ h+a+1 by omega),?_,?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · change a ≤ h+a+1; omega
    · have hh := hs q hq; omega
  · funext s
    simp only [tailProduct_cons, t, TailOperation.factor, ↓reduceIte]
    ring

theorem tail_separation {h : ℕ} (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (hF : ∀ i, F i ∈ VClass B h) {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hdetect : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hsupport : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (M i) s.val) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → C0Ball → ℝ,
      (∀ i, G i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (G i) (m (φ i))|) ∧
      Pairwise (fun i j => Disjoint (tsupport (G i)) (tsupport (G j))) := by
  have he : ∀ᶠ a in atTop, dyadic a < cstar/2 :=
    dyadic_tendsto.eventually (eventually_lt_nhds (half_pos hcstar))
  obtain ⟨a,ha⟩ := he.exists
  let H := h+a+1
  let f (i N : ℕ) (s : C0Ball) := F i s*tailFactor (dyadic a) (N+1) s.val
  have hf (i N : ℕ) : f i N ∈ VClass B H := VClass_mul_tail (hF i) a N
  obtain ⟨A,hA⟩ := VClass_pairing_bound B H
  have hconv (i : ℕ) : Tendsto
      (fun N => completedPairing (sourceClasses B) c0Origin (f i N) (m i)) atTop
      (nhds (completedPairing (sourceClasses B) c0Origin (F i) (m i))) := by
    apply (completedPairing_tendsto (sourceClasses B) c0Origin (f i) (F i) A
      (fun N => hA (f i N) (hf i N)) ?_).2
    intro s
    have hh := (tailFactor_tendsto_one (dyadic_pos a) s.val).comp
      (tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id)
    simpa only [f,mul_one,Function.comp_def,Nat.succ_eq_add_one] using hh.const_mul (F i s)
  have hchoose (i : ℕ) : ∃ N, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (f i N) (m i)| := by
    have hev := (Metric.tendsto_nhds.mp (hconv i)) (δ/2) (half_pos hδ)
    obtain ⟨N,hN⟩ := hev.exists
    refine ⟨N,?_⟩
    rw [Real.dist_eq] at hN
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (F i) (m i))
      (completedPairing (sourceClasses B) c0Origin (f i N) (m i))
    rw [abs_sub_comm] at hab
    linarith [hdetect i]
  choose N hN using hchoose
  obtain ⟨φ,hφ,hrel⟩ := thin_sequence (r := fun i j => N i+1 ≤ M j) (fun i =>
    hM.eventually (eventually_ge_atTop (N i+1)))
  refine ⟨H,φ,hφ,fun i => f (φ i) (N (φ i)),fun i => hf _ _,fun i => hN _,?_⟩
  have hdis (i j : ℕ) (hij : i<j) : Disjoint
      (tsupport (f (φ i) (N (φ i)))) (tsupport (f (φ j) (N (φ j)))) := by
    apply Set.disjoint_left.mpr
    intro s hi hj
    have hi' := tsupport_product_subset_right (F (φ i))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ i)+1) s.val) hi
    have hi'' := tsupport_comp_subset (tailFactor (dyadic a) (N (φ i)+1)) continuous_subtype_val hi'
    have hupper := tailFactor_support (dyadic_pos a) (N (φ i)+1) hi''
    have hj' := tsupport_product_subset_left (F (φ j))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ j)+1) s.val) hj
    have hlower := hsupport (φ j) s hj'
    have hord := tau_antitone s.val (hrel i j hij)
    change tau (N (φ i)+1) s.val ≤ 2*dyadic a at hupper
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hdis i j hlt
  · exact (hdis j i hgt).symm

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem tau_cubeExtend_restrict_le (I : Finset ℕ) (N : ℕ) (s : C0Ball) :
    tau N (cubeExtend I (cubeRestrict I s)).val ≤ tau N s.val := by
  classical
  apply c0_norm_le _ (tau_nonneg _ _)
  intro k
  rw [coordinateTail_apply]
  by_cases hk : N < k
  · simp only [hk, ↓reduceIte]
    change |extendFinite I (fun i => (cubeRestrict I s i).val) k| ≤ _
    rw [extendFinite_apply]
    split_ifs with hi
    · have hb := c0_norm_apply_le (coordinateTail N s.val) k
      simpa only [coordinateTail_apply,hk,↓reduceIte,tau,cubeRestrict] using hb
    · simpa using tau_nonneg N s.val
  · simpa only [hk,↓reduceIte,abs_zero] using tau_nonneg N s.val

structure RadiusLocalization {Γ : Type*} (B : CylinderBases Γ) where
  terminal : Γ → Prop
  firstCoordinate : Γ → ℕ
  finite_exceptions : ∀ j N, {γ | B.band γ ≤ j ∧ (terminal γ ∨ firstCoordinate γ ≤ N)}.Finite
  base_radius : ∀ γ, ¬terminal γ → ∀ N, N < firstCoordinate γ →
    ∀ x ∈ tsupport (B.base γ), B.ell (B.band γ) ≤ tau N (cubeExtend (B.coordinates γ) x).val

namespace RadiusLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

theorem representation_tail_lower {γ : Γ} (r : GeneratedRepresentation B γ)
    (ht : ¬loc.terminal γ) (N : ℕ) (hN : N < loc.firstCoordinate γ)
    (s : C0Ball) (hs : s ∈ tsupport r.value) :
    B.ell (B.band γ)/2 ≤ tau N s.val := by
  let φ : Cube (B.coordinates γ) → ℝ := fun x => -tau N (cubeExtend (B.coordinates γ) x).val
  have hφ : LipschitzWith 1 φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [φ,dist_neg_neg,NNReal.coe_one,one_mul]
    calc
      _ ≤ dist (cubeExtend (B.coordinates γ) x).val (cubeExtend (B.coordinates γ) y).val :=
        by simpa only [NNReal.coe_one,one_mul] using (tau_lipschitz N).dist_le_mul _ _
      _ ≤ dist x y := by
        simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq] using (cubeExtend_lipschitz (B.coordinates γ)).dist_le_mul x y
  have hb : ∀ x ∈ tsupport (B.base γ), φ x ≤ -B.ell (B.band γ) := by
    intro x hx
    exact neg_le_neg (loc.base_radius γ ht N hN x hx)
  have hh := r.support_bound hφ hb s hs
  have htau := tau_cubeExtend_restrict_le (B.coordinates γ) N s
  have hbudget := r.budget
  dsimp only [φ] at hh
  linarith

include loc in

theorem low_bands_disjoint (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h j : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i)=j) (hjh : j ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (hγ : Function.Injective γ) (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      Pairwise (fun i k => Disjoint (tsupport (F i)) (tsupport (F k))) := by
  have hgood (N : ℕ) : ∀ᶠ i in atTop, ¬loc.terminal (γ i) ∧ N < loc.firstCoordinate (γ i) := by
    have he := (hγ.tendsto_cofinite).eventually ((loc.finite_exceptions j N).eventually_cofinite_notMem)
    rw [Nat.cofinite_eq_atTop] at he
    filter_upwards [he] with i hi
    have hh : ¬(loc.terminal (γ i) ∨ loc.firstCoordinate (γ i) ≤ N) := by
      intro hn
      exact hi ⟨(hj i).le,hn⟩
    simpa only [not_or,not_le] using hh
  obtain ⟨ψ,hψ,hψgood⟩ := choose_mono_sequence hgood
  let f (i : ℕ) (s : C0Ball) := (r (ψ i)).value s*tailProduct (ts (ψ i)) s
  have hf (i : ℕ) : f i ∈ VClass B h :=
    ⟨γ (ψ i),r (ψ i),ts (ψ i),hr _,by rw [hj]; exact hjh,ht _,ha _,rfl⟩
  obtain ⟨H,η,hη,F,hF,hdet,hdis⟩ := tail_separation f (m ∘ ψ) hf hδ
    (half_pos (B.ell_pos j)) (fun i => hd (ψ i)) id tendsto_id (by
      intro i s hs
      have hsu := tsupport_product_subset_left (r (ψ i)).value (tailProduct (ts (ψ i))) hs
      have hh := loc.representation_tail_lower (r (ψ i)) (hψgood i).1 i (hψgood i).2 s hsu
      simpa only [hj,id_eq] using hh)
  exact ⟨H,ψ ∘ η,hψ.comp hη,F,hF,hdet,hdis⟩

end RadiusLocalization
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_supports_compatible {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (q : ℕ → Cube (B.coordinates γ)) (a b : ℕ → ℝ)
    (haPos : ∀ i, 0 < a i) (ha0 : Tendsto a atTop (nhds 0)) (hb0 : Tendsto b atTop (nhds 0))
    (hsup : ∀ i x, |(r i).cubeValue x| ≤ b i)
    (hsupp : ∀ i x, x ∈ tsupport (r i).cubeValue → dist x (q i) ≤ a i)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A+1)
          (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := q) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten (ts (ψ i)) h (hr _) hj (ht _) (ha _)
    v (m (ψ i)) (half_pos hδ) (haPos (ψ i))
  choose θ rr hcap hops hdif hflat hsupold using hfl
  have hmem (i : ℕ) : (fun s => (rr i).value s*tailProduct (ts (ψ i)) s) ∈ VClass B (h+1) := by
    refine ⟨γ,rr i,ts (ψ i),?_,hj.trans (Nat.le_succ _),(ht _).trans (Nat.le_succ _),
      fun t hm => (ha _ t hm).trans (Nat.le_succ _),rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  have hnew (i : ℕ) (s : C0Ball) (hs : s ∈ tsupport (rr i).value) :
      dist (cubeRestrict (B.coordinates γ) s) (q (ψ i)) ≤ 2*a (ψ i) := by
    have he : (rr i).cubeValue = (flattenOperation (B.coordinates γ) (θ i) v).act (r (ψ i)).cubeValue := by
      simp only [GeneratedRepresentation.cubeValue,hops i,applyOperations_append,applyOperations_cons,applyOperations_nil]
    have hcube := tsupport_comp_subset (rr i).cubeValue (cubeRestrict_lipschitz _).continuous hs
    rw [he] at hcube
    have hh := localOp_support_bound true (flattenOperation (B.coordinates γ) (θ i) v).point
      (dyadic_pos (θ i)) (r (ψ i)).cubeValue (fun x => dist x (q (ψ i)))
      (LipschitzWith.dist_left _) (a (ψ i)) (hsupp (ψ i)) _ hcube
    simp only [NNReal.coe_one] at hh
    linarith [hcap i]
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic (θ i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue (flattenOperation (B.coordinates γ) (θ i) v).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hrad : Tendsto (fun j => 2*a (ψ j)+dist (q (ψ j)) v) atTop (nhds 0) := by
      simpa only [Function.comp_def,mul_zero,dist_self,zero_add] using
        ((ha0.comp hψ.tendsto_atTop).const_mul 2).add (hvψ.dist (show Tendsto (fun _ : ℕ => v) atTop (nhds v) from tendsto_const_nhds))
    have he := hrad.eventually (eventually_lt_nhds
      (show (0 : ℝ)<3*dyadic (θ i)/8 by have := dyadic_pos (θ i); positivity))
    filter_upwards [he] with j hj
    intro s hs
    exact lt_of_le_of_lt ((dist_triangle _ (q (ψ j)) _).trans (add_le_add (hnew j s hs) le_rfl)) hj
  have hesmall : Tendsto (fun i => |e i| * ((h : ℝ≥0)*2^h : ℝ≥0)) atTop (nhds 0) := by
    have he0 : Tendsto (fun i => |e i|) atTop (nhds 0) := squeeze_zero
      (fun _ => abs_nonneg _) (fun i => hsup (ψ i) _) (hb0.comp hψ.tendsto_atTop)
    simpa only [zero_mul] using he0.mul_const (((h : ℝ≥0)*2^h : ℝ≥0) : ℝ)
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun i => tailProduct (ts (ψ i))) C e
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) ((h : ℝ≥0)*2^h)
    (fun i => (rr i).value_lipschitz.continuous)
    (fun i => tailProduct_lipschitz_bound _ h (ht _) (ha _))
    (fun i => by simpa only [Nat.cast_add,Nat.cast_one] using VClass_lipschitz B (h+1) (hmem i)) hC (fun i s hs => hflat i s hs) hnest hesmall
  refine ⟨ψ ∘ η,hψ.comp hη,fun i s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s,
    fun i => hmem _,?_,hLip⟩
  intro i
  have hb := hdif (η i)
  have hh := hd (ψ (η i))
  have hab := abs_sub_abs_le_abs_sub
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (r (ψ (η i))).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
  rw [abs_sub_comm] at hab
  change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin
    (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i)))|
  linarith

end
end C0Absorption

end OAI
