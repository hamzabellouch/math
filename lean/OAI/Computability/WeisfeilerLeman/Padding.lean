import OAI.Computability.WeisfeilerLeman.Marking

namespace OAI

universe uV uW uD uP uE uT uL uA uB

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

theorem degree_detect_base (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e : V ≃ W) (hc : ∀ v, c v = d (e v))
    (q : ℕ) (hN : 2 ≤ Fintype.card V) (x : V)
    (y : Vertex W (fun v => code (d v)*(Fintype.card V+1)) q)
    (hd : Pebble.degree (graph G (fun v => code (c v)*(Fintype.card V+1)) q) (.base x) =
      Pebble.degree (graph H (fun v => code (d v)*(Fintype.card V+1)) q) y) :
    ∃ z, y = .base z ∧ c x = d z := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hx : 2 < Pebble.degree (graph G (fun v => code (c v)*(Fintype.card V+1)) q) (.base x) := by
    rw [degree_base]
    have hm := Nat.mul_le_mul_right (Fintype.card V+1) (hpos (c x))
    nlinarith
  cases y with
  | base z =>
    refine ⟨z,rfl,hcode ?_⟩
    rw [degree_base,degree_base] at hd
    exact code_of_degree (base_degree_lt G x) (hcard ▸ base_degree_lt H z) hd
  | mark z i => rw [degree_mark] at hd; omega
  | pad i => rw [degree_pad] at hd; omega
  | hub =>
    have hsum : (∑ v : W, code (d v)*(Fintype.card V+1)) =
        ∑ v : V, code (c v)*(Fintype.card V+1) := by
      rw [← e.sum_comp (fun v => code (d v)*(Fintype.card V+1))]
      simp_rw [← hc]
    have hh := hub_above_base G (fun v => code (c v)*(Fintype.card V+1)) q hN
      (fun v => Nat.mul_pos (hpos (c v)) (by omega)) x
    rw [degree_hub] at hd hh
    rw [← hcard,hsum] at hd
    omega

def basePosition {K : ℕ} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}
    (P : Pebble.Position K V W) : Pebble.Position K (Vertex V count q) (Vertex W count' q) :=
  fun i => (P i).map (fun xy => (.base xy.1,.base xy.2))

omit [Fintype V] [Fintype W] in
@[simp] theorem basePosition_update {K : ℕ} {count : V → ℕ} {count' : W → ℕ} {q : ℕ}
    (P : Pebble.Position K V W) (i : Fin K) (x : V) (y : W) :
    (basePosition (count := count) (count' := count') (q := q) (Function.update P i (some (x,y)))) =
      Function.update (basePosition P) i (some (.base x,.base y)) := by
  funext j
  by_cases h : j=i
  · subst j; simp [basePosition]
  · simp [basePosition,h]

theorem wins_bases (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e₀ : V ≃ W) (hc : ∀ v, c v = d (e₀ v))
    (q K : ℕ) (hN : 2 ≤ Fintype.card V) (hK : 2 ≤ K)
    (h : Pebble.Wins (graph G (fun v => code (c v)*(Fintype.card V+1)) q)
      (graph H (fun v => code (d v)*(Fintype.card V+1)) q) (fun _ _ => True)
      (fun _ : Fin K => none)) :
    Pebble.Wins G H (fun v w => c v = d w) (fun _ : Fin K => none) := by
  classical
  let J : Pebble.Invariant G H (fun v w => c v = d w) K := {
    safe := fun P => Pebble.Wins (graph G (fun v => code (c v)*(Fintype.card V+1)) q)
      (graph H (fun v => code (d v)*(Fintype.card V+1)) q) (fun _ _ => True) (basePosition P)
    forget := by
      intro P Q hQ hPQ
      refine hQ.forget (fun i => ?_)
      rcases hPQ i with hi | hi
      · exact Or.inl (by simp [basePosition,hi])
      · exact Or.inr (by simp [basePosition,hi])
    atomic := by
      intro P hP
      constructor
      · intro i x y hi
        have hdi := hP.degree_eq hK (i := i) (x := .base x) (y := .base y) (by simp [basePosition,hi])
        obtain ⟨z,hz,hcz⟩ := degree_detect_base G H c d code hcode hpos e₀ hc q hN x (.base y) hdi
        cases Vertex.base.inj hz
        exact hcz
      · intro i j x y u v hi hj
        have hh := hP.atomic.2 i j (.base x) (.base y) (.base u) (.base v)
          (by simp [basePosition,hi]) (by simp [basePosition,hj])
        simpa only [Vertex.base.injEq,graph,Adj] using hh
    extend := by
      intro P hP i hi
      obtain ⟨e,he⟩ := hP.extend i (by simp [basePosition,hi])
      have hb (x : V) : ∃ y, e (.base x) = .base y ∧ c x = d y := by
        exact degree_detect_base G H c d code hcode hpos e₀ hc q hN x (e (.base x))
          ((he (.base x)).degree_eq hK (Function.update_self _ _ _))
      choose f hf hcf using hb
      have hinj : Function.Injective f := by
        intro x y hxy
        exact Vertex.base.inj (e.injective (by rw [hf,hf,hxy]))
      let eb : V ≃ W := Equiv.ofBijective f
        ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,Fintype.card_congr e₀⟩)
      refine ⟨eb,fun x => ?_⟩
      rw [basePosition_update]
      simpa only [hf,eb,Equiv.ofBijective_apply] using he (.base x) }
  refine ⟨J,?_⟩
  unfold J basePosition
  exact h

end WLTime.Marking

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} [Fintype P] [Fintype E]
    (I : ConsistencyData (r+1) m P E)

noncomputable def baseEquiv (K : ℕ) (hr : 1 ≤ r) : I.Vertex K 0 ≃ I.Vertex K 1 :=
  Equiv.sigmaCongrRight (fun b => I.translate K b.val
    (Classical.choice (I.legal_nonempty K hr 1 b.val)))

omit [Fintype P] [Fintype E] in
@[simp] theorem baseEquiv_block (K : ℕ) (hr : 1 ≤ r) (x : I.Vertex K 0) :
    (I.baseEquiv K hr x).1 = x.1 := rfl

noncomputable def blockCode (K : ℕ) (b : I.Block K) : ℕ :=
  (Fintype.equivFin (I.Block K) b).val + 1

theorem blockCode_injective (K : ℕ) : Function.Injective (I.blockCode K) := by
  intro b c h
  apply (Fintype.equivFin (I.Block K)).injective
  apply Fin.ext
  simpa only [blockCode,Nat.add_right_cancel_iff] using h

theorem blockCode_pos (K : ℕ) (b : I.Block K) : 0 < I.blockCode K b := Nat.zero_lt_succ _

noncomputable def markCount (K : ℕ) (b : I.Block K) : ℕ :=
  I.blockCode K b * (Fintype.card (I.Vertex K 0)+1)

abbrev MarkedVertex (K : ℕ) (ε : F₂) (q : ℕ) :=
  Marking.Vertex (I.Vertex K ε) (fun v => I.markCount K v.1) q

noncomputable def markedGraph (K : ℕ) (ε : F₂) (q : ℕ) :
    SimpleGraph (I.MarkedVertex K ε q) :=
  Marking.graph (I.valuationGraph K ε) (fun v => I.markCount K v.1) q

theorem marked_diameter_two (K : ℕ) (ε : F₂) (q : ℕ) (x y : I.MarkedVertex K ε q) :
    x=y ∨ (I.markedGraph K ε q).Adj x y ∨
      ∃ z, (I.markedGraph K ε q).Adj x z ∧ (I.markedGraph K ε q).Adj z y :=
  Marking.diameter_two _ x y

noncomputable def markedEquiv (K : ℕ) (hr : 1 ≤ r) (q : ℕ) :
    I.MarkedVertex K 0 q ≃ I.MarkedVertex K 1 q :=
  Marking.liftEquiv (I.baseEquiv K hr) (fun _ => rfl)

theorem card_marked_eq (K : ℕ) (hr : 1 ≤ r) (q : ℕ) :
    Fintype.card (I.MarkedVertex K 0 q) = Fintype.card (I.MarkedVertex K 1 q) :=
  Fintype.card_congr (I.markedEquiv K hr q)

theorem two_le_card_base [Nonempty P] (K : ℕ) (hm : 2 ≤ m) :
    2 ≤ Fintype.card (I.Vertex K 0) := by
  classical
  let p : P := Classical.choice inferInstance
  let z : Fin m := ⟨0,by omega⟩
  let f : Fin m → I.Vertex K 0 := fun a =>
    ⟨⟨.site 0 (.inl p) a z,True.intro,True.intro⟩,I.zeroValuation K _⟩
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg (fun x : I.Vertex K 0 => x.1.val) h
    exact (BlockName.site.inj he).2.2.1
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

theorem marked_wins_iff_ac [Nonempty P] (hr : 2 ≤ r) (hm : 2 ≤ m) (q : ℕ) :
    Pebble.Wins (I.markedGraph (r+2) 0 q) (I.markedGraph (r+2) 1 q)
      (fun _ _ => True) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  constructor
  · intro h
    apply (I.colored_wins_iff_ac hr).mp
    exact Marking.wins_bases (I.valuationGraph (r+2) 0) (I.valuationGraph (r+2) 1)
      Sigma.fst Sigma.fst (I.blockCode (r+2)) (I.blockCode_injective (r+2))
      (I.blockCode_pos (r+2)) (I.baseEquiv (r+2) (by omega)) (fun _ => rfl)
      q (r+2) (I.two_le_card_base (r+2) hm) (by omega) h
  · intro h
    obtain ⟨Q⟩ := I.arcConsistent_iff.mp h
    exact (Marking.liftSystem Sigma.fst Sigma.fst (I.markCount (r+2)) q (r+2)
      (I.valuationSystem Q (r+2) (by omega) hr le_rfl)).wins_empty

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression

noncomputable def BlockName.equivProduct {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA} :
    BlockName r T L A ≃ Fin (r+1) × (T ⊕ L) × A × A where
  toFun
    | .site i t a b => (i,.inl t,a,b)
    | .square i l a b => (i,.inr l,a,b)
  invFun
    | (i,.inl t,a,b) => .site i t a b
    | (i,.inr l,a,b) => .square i l a b
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i,t | l,a,b⟩ <;> rfl

theorem BlockName.card {r : ℕ} {T : Type uT} {L : Type uL} {A : Type uA} [Fintype T] [Fintype L] [Fintype A] :
    Fintype.card (BlockName r T L A) =
      (r+1)*(Fintype.card T+Fintype.card L)*(Fintype.card A)^2 := by
  rw [Fintype.card_congr BlockName.equivProduct]
  simp only [Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]
  ring

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} [Fintype P] [Fintype E]
    (I : ConsistencyData (r+1) m P E)

noncomputable def blockCoefficient (_I : ConsistencyData (r+1) m P E) (K : ℕ) : ℕ :=
  (r+1)*(Fintype.card P+Fintype.card E*(8*K+1))

theorem card_blocks_le (K : ℕ) : Fintype.card (I.Block K) ≤ I.blockCoefficient K*m^2 := by
  classical
  calc
    _ ≤ Fintype.card (RawBlock (r := r) (m := m) (P := P) (E := E) K) :=
      Fintype.card_subtype_le _
    _ = _ := by
      rw [BlockName.card]
      simp only [TypeNode,TypeLink,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
        blockCoefficient]
      ring

omit [Fintype P] [Fintype E] in
theorem footprint_card_le (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) :
    (I.footprint K b).card ≤ 4 := by
  classical
  cases b <;> simp only [footprint]
  · simp
  · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
        ((Finset.card_insert_le _ _).trans (by simp)))))

omit [Fintype P] [Fintype E] in
theorem card_readValue_le (K D : ℕ) (hD : 2 ≤ D) (hp : ∀ p, 2^(I.dim p) ≤ D)
    (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    Fintype.card (I.ReadValue K n) ≤ D := by
  cases n with
  | horizontal i t a b =>
    cases t with
    | inl p => simpa [ReadValue,Value,F₂,ZMod.card] using hp p
    | inr ej => simpa [ReadValue,Value,F₂,ZMod.card] using hD
  | vertical => simpa [ReadValue,F₂,ZMod.card] using hD

theorem card_legal_le (K D : ℕ) (hD : 2 ≤ D) (hp : ∀ p, 2^(I.dim p) ≤ D)
    (ε : F₂) (b : I.Block K) : Fintype.card (I.Legal K ε b.val) ≤ D^4 := by
  classical
  let f : I.Legal K ε b.val → ((n : {n // n ∈ I.footprint K b.val}) → I.ReadValue K n.val) :=
    fun R n => R.val.val n.val
  have hf : Function.Injective f := by
    intro R S h
    apply Subtype.ext
    apply Subtype.ext
    funext n
    by_cases hn : n ∈ I.footprint K b.val
    · exact congrFun h ⟨n,hn⟩
    · exact (R.val.property n hn).trans (S.val.property n hn).symm
  calc
    _ ≤ Fintype.card ((n : {n // n ∈ I.footprint K b.val}) → I.ReadValue K n.val) :=
      Fintype.card_le_of_injective f hf
    _ = ∏ n : {n // n ∈ I.footprint K b.val}, Fintype.card (I.ReadValue K n.val) :=
      Fintype.card_pi
    _ ≤ ∏ _n : {n // n ∈ I.footprint K b.val}, D :=
      Finset.prod_le_prod (fun n _ => I.card_readValue_le K D hD hp n.val)
    _ = D^(I.footprint K b.val).card := by simp
    _ ≤ D^4 := Nat.pow_le_pow_right (by omega) (I.footprint_card_le K b.val)

theorem card_bases_le (K D : ℕ) (hD : 2 ≤ D) (hp : ∀ p, 2^(I.dim p) ≤ D) (ε : F₂) :
    Fintype.card (I.Vertex K ε) ≤ I.blockCoefficient K*D^4*m^2 := by
  classical
  calc
    _ = ∑ b : I.Block K, Fintype.card (I.Legal K ε b.val) := Fintype.card_sigma
    _ ≤ ∑ _b : I.Block K, D^4 := Finset.sum_le_sum (fun b _ => I.card_legal_le K D hD hp ε b)
    _ = Fintype.card (I.Block K)*D^4 := by simp
    _ ≤ (I.blockCoefficient K*m^2)*D^4 := Nat.mul_le_mul_right _ (I.card_blocks_le K)
    _ = _ := by ring

theorem card_blocks_le_bases (K : ℕ) : Fintype.card (I.Block K) ≤ Fintype.card (I.Vertex K 0) := by
  exact Fintype.card_le_of_injective (fun b : I.Block K => (⟨b,I.zeroValuation K b.val⟩ : I.Vertex K 0))
    (fun _ _ h => congrArg Sigma.fst h)

theorem marked_order_cubic (K q : ℕ) :
    Fintype.card (I.MarkedVertex K 0 q) ≤ (Fintype.card (I.Vertex K 0)+1)^3+q := by
  classical
  rw [Marking.card_vertices]
  have hmark (v : I.Vertex K 0) : I.markCount K v.1 ≤
      Fintype.card (I.Vertex K 0)*(Fintype.card (I.Vertex K 0)+1) := by
    apply Nat.mul_le_mul_right
    exact (Nat.succ_le_iff.mpr (Fintype.equivFin (I.Block K) v.1).isLt).trans (I.card_blocks_le_bases K)
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (I.Vertex K 0))) => hmark v)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  nlinarith

theorem marked_order_six (K D : ℕ) (hm : 1 ≤ m) (hD : 2 ≤ D)
    (hp : ∀ p, 2^(I.dim p) ≤ D) (q : ℕ) :
    Fintype.card (I.MarkedVertex K 0 q) ≤ (I.blockCoefficient K*D^4+1)^3*m^6+q := by
  have hN := I.card_bases_le K D hD hp 0
  have hm2 : 1 ≤ m^2 := Nat.one_le_pow _ _ hm
  calc
    _ ≤ (Fintype.card (I.Vertex K 0)+1)^3+q := I.marked_order_cubic K q
    _ ≤ (I.blockCoefficient K*D^4*m^2+1)^3+q := by gcongr
    _ ≤ ((I.blockCoefficient K*D^4+1)*m^2)^3+q := by gcongr; nlinarith
    _ = _ := by ring

end ConsistencyData
end WLTime.Compression

namespace WLTime

noncomputable def Graph.ofSimple {V : Type uV} {n : ℕ} (G : SimpleGraph V) (e : V ≃ Fin n) : Graph n := by
  classical
  exact ⟨fun x y => decide (G.Adj (e.symm x) (e.symm y)),
    (by intro x y; simp only [decide_eq_decide]; exact G.adj_comm _ _),fun x => by simp⟩

def Graph.simple {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj x y := G.adj x y = true
  symm := ⟨fun x y h => (G.property.1 y x).trans h⟩
  loopless := ⟨fun x h => Bool.false_ne_true ((G.property.2 x).symm.trans h)⟩

@[simp] theorem Graph.ofSimple_adj {V : Type uV} {n : ℕ} (G : SimpleGraph V)
    (e : V ≃ Fin n) (x y : V) :
    ((Graph.ofSimple G e).simple).Adj (e x) (e y) ↔ G.Adj x y := by
  simp [Graph.ofSimple,Graph.simple,Graph.adj]

@[simp] theorem Graph.ofSimple_diameter {V : Type uV} {n : ℕ} (G : SimpleGraph V)
    (e : V ≃ Fin n) (hn : 0 < n)
    (h : ∀ x y, x=y ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y) :
    (Graph.ofSimple G e).diameterTwo := by
  refine ⟨hn,fun x y => ?_⟩
  rcases h (e.symm x) (e.symm y) with he | he | ⟨z,hz,hz'⟩
  · exact Or.inl (e.symm.injective he)
  · exact Or.inr (Or.inl (by simpa [Graph.ofSimple,Graph.adj] using he))
  · exact Or.inr (Or.inr ⟨e z,by simpa [Graph.ofSimple,Graph.adj] using hz,
      by simpa [Graph.ofSimple,Graph.adj] using hz'⟩)

theorem pebble_iff_wins {n K : ℕ} (G H : Graph n) (P : Position K n) :
    Pebble.Wins G.simple H.simple (fun _ _ => True) P ↔ Wins G H P := by
  constructor
  · rintro ⟨I,hI⟩
    let J : GameInvariant G H K := {
      safe := I.safe
      forget := I.forget
      atomic := by
        intro Q hQ i j x y u v hi hj
        obtain ⟨he,ha⟩ := (I.atomic hQ).2 i j x y u v hi hj
        refine ⟨he,?_⟩
        change (G.adj x u = true ↔ H.adj y v = true) at ha
        cases hg : G.adj x u <;> cases hh : H.adj y v <;> simp_all
      extend := I.extend }
    exact ⟨J,hI⟩
  · rintro ⟨I,hI⟩
    let J : Pebble.Invariant G.simple H.simple (fun _ _ => True) K := {
      safe := I.safe
      forget := I.forget
      atomic := by
        intro Q hQ
        refine ⟨fun _ _ _ _ => True.intro,?_⟩
        intro i j x y u v hi hj
        obtain ⟨he,ha⟩ := I.atomic hQ i j x y u v hi hj
        exact ⟨he,by change (_ = true ↔ _ = true); rw [ha]⟩
      extend := I.extend }
    exact ⟨J,hI⟩

theorem wins_ofSimple_iff {A : Type uA} {B : Type uB} {n K : ℕ} (G : SimpleGraph A) (H : SimpleGraph B)
    (e : A ≃ Fin n) (f : B ≃ Fin n) :
    Wins (Graph.ofSimple G e) (Graph.ofSimple H f) (fun _ : Fin K => none) ↔
      Pebble.Wins G H (fun _ _ => True) (fun _ : Fin K => none) := by
  rw [← pebble_iff_wins]
  constructor
  · intro h
    have hh := h.transport (G' := G) (H' := H) e.symm f.symm
      (fun x y => by simp [Graph.ofSimple,Graph.simple,Graph.adj])
      (fun x y => by simp [Graph.ofSimple,Graph.simple,Graph.adj])
    simpa only [Pebble.Position.map_none] using hh
  · intro h
    have hh := h.transport e f (fun x y => (Graph.ofSimple_adj G e x y).symm)
      (fun x y => (Graph.ofSimple_adj H f x y).symm)
    simpa only [Pebble.Position.map_none] using hh

end WLTime

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} [Fintype P] [Fintype E]
    (I : ConsistencyData (r+1) m P E)

theorem marked_padding_order (K q : ℕ) :
    Fintype.card (I.MarkedVertex K 0 q) = Fintype.card (I.MarkedVertex K 0 0)+q := by
  rw [Marking.card_vertices,Marking.card_vertices]

theorem matrix_compression [Nonempty P] (hr : 2 ≤ r) (hm : 2 ≤ m) (n : ℕ)
    (hn : Fintype.card (I.MarkedVertex (r+2) 0 0) ≤ n) :
    ∃ G H : Graph n, G.diameterTwo ∧ H.diameterTwo ∧
      (Equivalent .joint (r+1) G H ↔ I.ArcConsistent) ∧
      (Equivalent .separate (r+2) G H ↔ I.ArcConsistent) := by
  classical
  let q := n-Fintype.card (I.MarkedVertex (r+2) 0 0)
  have hcard : Fintype.card (I.MarkedVertex (r+2) 0 q) = n := by
    rw [I.marked_padding_order]
    exact Nat.add_sub_of_le hn
  let e : I.MarkedVertex (r+2) 0 q ≃ Fin n :=
    (Fintype.equivFin _).trans (finCongr hcard)
  let f : I.MarkedVertex (r+2) 1 q ≃ Fin n :=
    (I.markedEquiv (r+2) (by omega) q).symm.trans e
  have hnpos : 0 < n := hcard ▸ Fintype.card_pos_iff.mpr ⟨Marking.Vertex.hub⟩
  let G := Graph.ofSimple (I.markedGraph (r+2) 0 q) e
  let H := Graph.ofSimple (I.markedGraph (r+2) 1 q) f
  refine ⟨G,H,Graph.ofSimple_diameter _ _ hnpos (I.marked_diameter_two _ _ _),
    Graph.ofSimple_diameter _ _ hnpos (I.marked_diameter_two _ _ _),?_,?_⟩
  · exact (joint_equivalent_iff_wins hnpos (by omega)).trans
      ((wins_ofSimple_iff _ _ e f).trans (I.marked_wins_iff_ac hr hm q))
  · exact (separate_equivalent_iff_wins hnpos).trans
      ((wins_ofSimple_iff _ _ e f).trans (I.marked_wins_iff_ac hr hm q))

theorem matrix_compression_six [Nonempty P] (hr : 2 ≤ r) (hm : 2 ≤ m)
    (D : ℕ) (hD : 2 ≤ D) (hp : ∀ p, 2^(I.dim p) ≤ D) (n : ℕ)
    (hn : (I.blockCoefficient (r+2)*D^4+1)^3*m^6 ≤ n) :
    ∃ G H : Graph n, G.diameterTwo ∧ H.diameterTwo ∧
      (Equivalent .joint (r+1) G H ↔ I.ArcConsistent) ∧
      (Equivalent .separate (r+2) G H ↔ I.ArcConsistent) := by
  apply I.matrix_compression hr hm n
  have h := I.marked_order_six (r+2) D (by omega) hD hp 0
  simp only [Nat.add_zero] at h
  exact h.trans hn

end ConsistencyData
end WLTime.Compression

end OAI
