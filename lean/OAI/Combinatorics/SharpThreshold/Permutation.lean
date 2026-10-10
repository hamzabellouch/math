import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem permEdge_refl {n : ℕ} (e : GraphEdge n) :
    permEdge (Equiv.refl _) e = e := by
  apply Subtype.ext
  simp [permEdge]

@[simp] theorem permEdge_permEdge {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (e : GraphEdge n) :
    permEdge π (permEdge ρ e) = permEdge (ρ.trans π) e := by
  apply Subtype.ext
  simp [permEdge, Finset.map_map]

@[simp] theorem permEdge_symm_permEdge {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π.symm (permEdge π e) = e := by
  simp

@[simp] theorem permEdge_permEdge_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π (permEdge π.symm e) = e := by
  simp

def permEdgeEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) : GraphEdge n ≃ GraphEdge n where
  toFun := permEdge π
  invFun := permEdge π.symm
  left_inv := permEdge_symm_permEdge π
  right_inv := permEdge_permEdge_symm π

@[simp] theorem permuteConfig_refl {n : ℕ} (x : GraphConfig n) :
    permuteConfig (Equiv.refl _) x = x := by
  funext e
  simp [permuteConfig]

@[simp] theorem permuteConfig_perm {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (x : GraphConfig n) :
    permuteConfig π (permuteConfig ρ x) = permuteConfig (ρ.trans π) x := by
  funext e
  simp [permuteConfig, permEdge_permEdge]

@[simp] theorem permuteConfig_symm_permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π.symm (permuteConfig π x) = x := by
  simp

@[simp] theorem permuteConfig_permuteConfig_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π (permuteConfig π.symm x) = x := by
  simp

def permuteConfigEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) :
    GraphConfig n ≃ GraphConfig n where
  toFun := permuteConfig π
  invFun := permuteConfig π.symm
  left_inv := permuteConfig_symm_permuteConfig π
  right_inv := permuteConfig_permuteConfig_symm π

theorem permEdge_transitive {n : ℕ} (e e' : GraphEdge n) :
    ∃ π : Equiv.Perm (Fin n), permEdge π e = e' := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq e.val e'.val (e.property.trans e'.property.symm)
  exact ⟨π, Subtype.ext hπ⟩

@[simp] theorem graphWeight_permuteConfig {n : ℕ} (p : ℝ)
    (π : Equiv.Perm (Fin n)) (x : GraphConfig n) :
    graphWeight p (permuteConfig π x) = graphWeight p x := by
  classical
  exact (permEdgeEquiv π.symm).prod_comp (fun e => if x e = true then p else 1 - p)

@[simp] theorem permuteConfig_update {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) (e : GraphEdge n) (b : Bool) :
    permuteConfig π (Function.update x e b) =
      Function.update (permuteConfig π x) (permEdge π e) b := by
  classical
  exact Function.update_comp_equiv x (permEdgeEquiv π.symm) e b

theorem edgeInfluence_permEdge {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (π : Equiv.Perm (Fin n)) (e : GraphEdge n) :
    edgeInfluence p f (permEdge π e) = edgeInfluence p f e := by
  classical
  unfold edgeInfluence
  rw [← (permuteConfigEquiv π).sum_comp]
  change (∑ x : GraphConfig n,
    if f (Function.update (permuteConfig π x) (permEdge π e) true) ≠
      f (Function.update (permuteConfig π x) (permEdge π e) false)
    then graphWeight p (permuteConfig π x) else 0) = _
  simp_rw [← permuteConfig_update, hf π, graphWeight_permuteConfig]

theorem edgeInfluence_eq {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (e e' : GraphEdge n) :
    edgeInfluence p f e = edgeInfluence p f e' := by
  obtain ⟨π, rfl⟩ := permEdge_transitive e e'
  exact (edgeInfluence_permEdge p f hf π e).symm

theorem totalInfluence_eq_card_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (e : GraphEdge n) :
    totalInfluence p f = Fintype.card (GraphEdge n) * edgeInfluence p f e := by
  classical
  unfold totalInfluence
  simp_rw [edgeInfluence_eq p f hf _ e]
  simp

end Problem313

end

end OAI
