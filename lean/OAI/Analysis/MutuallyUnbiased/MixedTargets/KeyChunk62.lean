import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound62
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1984 : keyMomentRows (1984 : Fin 2886) =
    keyMomentRow1984 := by decide +kernel

theorem keyMomentRowsAt1985 : keyMomentRows (1985 : Fin 2886) =
    keyMomentRow1985 := by decide +kernel

theorem keyMomentRowsAt1986 : keyMomentRows (1986 : Fin 2886) =
    keyMomentRow1986 := by decide +kernel

theorem keyMomentRowsAt1987 : keyMomentRows (1987 : Fin 2886) =
    keyMomentRow1987 := by decide +kernel

theorem keyMomentRowsAt1988 : keyMomentRows (1988 : Fin 2886) =
    keyMomentRow1988 := by decide +kernel

theorem keyMomentRowsAt1989 : keyMomentRows (1989 : Fin 2886) =
    keyMomentRow1989 := by decide +kernel

theorem keyMomentRowsAt1990 : keyMomentRows (1990 : Fin 2886) =
    keyMomentRow1990 := by decide +kernel

theorem keyMomentRowsAt1991 : keyMomentRows (1991 : Fin 2886) =
    keyMomentRow1991 := by decide +kernel

theorem keyMomentRowsAt1992 : keyMomentRows (1992 : Fin 2886) =
    keyMomentRow1992 := by decide +kernel

theorem keyMomentRowsAt1993 : keyMomentRows (1993 : Fin 2886) =
    keyMomentRow1993 := by decide +kernel

theorem keyMomentRowsAt1994 : keyMomentRows (1994 : Fin 2886) =
    keyMomentRow1994 := by decide +kernel

theorem keyMomentRowsAt1995 : keyMomentRows (1995 : Fin 2886) =
    keyMomentRow1995 := by decide +kernel

theorem keyMomentRowsAt1996 : keyMomentRows (1996 : Fin 2886) =
    keyMomentRow1996 := by decide +kernel

theorem keyMomentRowsAt1997 : keyMomentRows (1997 : Fin 2886) =
    keyMomentRow1997 := by decide +kernel

theorem keyMomentRowsAt1998 : keyMomentRows (1998 : Fin 2886) =
    keyMomentRow1998 := by decide +kernel

theorem keyMomentRowsAt1999 : keyMomentRows (1999 : Fin 2886) =
    keyMomentRow1999 := by decide +kernel

theorem keyMomentRowsAt2000 : keyMomentRows (2000 : Fin 2886) =
    keyMomentRow2000 := by decide +kernel

theorem keyMomentRowsAt2001 : keyMomentRows (2001 : Fin 2886) =
    keyMomentRow2001 := by decide +kernel

theorem keyMomentRowsAt2002 : keyMomentRows (2002 : Fin 2886) =
    keyMomentRow2002 := by decide +kernel

theorem keyMomentRowsAt2003 : keyMomentRows (2003 : Fin 2886) =
    keyMomentRow2003 := by decide +kernel

theorem keyMomentRowsAt2004 : keyMomentRows (2004 : Fin 2886) =
    keyMomentRow2004 := by decide +kernel

theorem keyMomentRowsAt2005 : keyMomentRows (2005 : Fin 2886) =
    keyMomentRow2005 := by decide +kernel

theorem keyMomentRowsAt2006 : keyMomentRows (2006 : Fin 2886) =
    keyMomentRow2006 := by decide +kernel

theorem keyMomentRowsAt2007 : keyMomentRows (2007 : Fin 2886) =
    keyMomentRow2007 := by decide +kernel

theorem keyMomentRowsAt2008 : keyMomentRows (2008 : Fin 2886) =
    keyMomentRow2008 := by decide +kernel

theorem keyMomentRowsAt2009 : keyMomentRows (2009 : Fin 2886) =
    keyMomentRow2009 := by decide +kernel

theorem keyMomentRowsAt2010 : keyMomentRows (2010 : Fin 2886) =
    keyMomentRow2010 := by decide +kernel

theorem keyMomentRowsAt2011 : keyMomentRows (2011 : Fin 2886) =
    keyMomentRow2011 := by decide +kernel

theorem keyMomentRowsAt2012 : keyMomentRows (2012 : Fin 2886) =
    keyMomentRow2012 := by decide +kernel

theorem keyMomentRowsAt2013 : keyMomentRows (2013 : Fin 2886) =
    keyMomentRow2013 := by decide +kernel

theorem keyMomentRowsAt2014 : keyMomentRows (2014 : Fin 2886) =
    keyMomentRow2014 := by decide +kernel

theorem keyMomentRowsAt2015 : keyMomentRows (2015 : Fin 2886) =
    keyMomentRow2015 := by decide +kernel

theorem keyMomentChunkSound62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 62) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1984 ∨ k.val = 1985 ∨ k.val = 1986 ∨ k.val = 1987 ∨ k.val = 1988 ∨ k.val = 1989 ∨ k.val = 1990 ∨ k.val = 1991 ∨ k.val = 1992 ∨ k.val = 1993 ∨ k.val = 1994 ∨ k.val = 1995 ∨ k.val = 1996 ∨ k.val = 1997 ∨ k.val = 1998 ∨ k.val = 1999 ∨ k.val = 2000 ∨ k.val = 2001 ∨ k.val = 2002 ∨ k.val = 2003 ∨ k.val = 2004 ∨ k.val = 2005 ∨ k.val = 2006 ∨ k.val = 2007 ∨ k.val = 2008 ∨ k.val = 2009 ∨ k.val = 2010 ∨ k.val = 2011 ∨ k.val = 2012 ∨ k.val = 2013 ∨ k.val = 2014 ∨ k.val = 2015 := by omega
  rcases heq with h1984 | h1985 | h1986 | h1987 | h1988 | h1989 | h1990 | h1991 | h1992 | h1993 | h1994 | h1995 | h1996 | h1997 | h1998 | h1999 | h2000 | h2001 | h2002 | h2003 | h2004 | h2005 | h2006 | h2007 | h2008 | h2009 | h2010 | h2011 | h2012 | h2013 | h2014 | h2015
  · have he : k = (1984 : Fin 2886) := Fin.ext h1984
    subst k
    rw [keyMomentRowsAt1984]
    exact keyMoment1984 B hB
  · have he : k = (1985 : Fin 2886) := Fin.ext h1985
    subst k
    rw [keyMomentRowsAt1985]
    exact keyMoment1985 B hB
  · have he : k = (1986 : Fin 2886) := Fin.ext h1986
    subst k
    rw [keyMomentRowsAt1986]
    exact keyMoment1986 B hB
  · have he : k = (1987 : Fin 2886) := Fin.ext h1987
    subst k
    rw [keyMomentRowsAt1987]
    exact keyMoment1987 B hB
  · have he : k = (1988 : Fin 2886) := Fin.ext h1988
    subst k
    rw [keyMomentRowsAt1988]
    exact keyMoment1988 B hB
  · have he : k = (1989 : Fin 2886) := Fin.ext h1989
    subst k
    rw [keyMomentRowsAt1989]
    exact keyMoment1989 B hB
  · have he : k = (1990 : Fin 2886) := Fin.ext h1990
    subst k
    rw [keyMomentRowsAt1990]
    exact keyMoment1990 B hB
  · have he : k = (1991 : Fin 2886) := Fin.ext h1991
    subst k
    rw [keyMomentRowsAt1991]
    exact keyMoment1991 B hB
  · have he : k = (1992 : Fin 2886) := Fin.ext h1992
    subst k
    rw [keyMomentRowsAt1992]
    exact keyMoment1992 B hB
  · have he : k = (1993 : Fin 2886) := Fin.ext h1993
    subst k
    rw [keyMomentRowsAt1993]
    exact keyMoment1993 B hB
  · have he : k = (1994 : Fin 2886) := Fin.ext h1994
    subst k
    rw [keyMomentRowsAt1994]
    exact keyMoment1994 B hB
  · have he : k = (1995 : Fin 2886) := Fin.ext h1995
    subst k
    rw [keyMomentRowsAt1995]
    exact keyMoment1995 B hB
  · have he : k = (1996 : Fin 2886) := Fin.ext h1996
    subst k
    rw [keyMomentRowsAt1996]
    exact keyMoment1996 B hB
  · have he : k = (1997 : Fin 2886) := Fin.ext h1997
    subst k
    rw [keyMomentRowsAt1997]
    exact keyMoment1997 B hB
  · have he : k = (1998 : Fin 2886) := Fin.ext h1998
    subst k
    rw [keyMomentRowsAt1998]
    exact keyMoment1998 B hB
  · have he : k = (1999 : Fin 2886) := Fin.ext h1999
    subst k
    rw [keyMomentRowsAt1999]
    exact keyMoment1999 B hB
  · have he : k = (2000 : Fin 2886) := Fin.ext h2000
    subst k
    rw [keyMomentRowsAt2000]
    exact keyMoment2000 B hB
  · have he : k = (2001 : Fin 2886) := Fin.ext h2001
    subst k
    rw [keyMomentRowsAt2001]
    exact keyMoment2001 B hB
  · have he : k = (2002 : Fin 2886) := Fin.ext h2002
    subst k
    rw [keyMomentRowsAt2002]
    exact keyMoment2002 B hB
  · have he : k = (2003 : Fin 2886) := Fin.ext h2003
    subst k
    rw [keyMomentRowsAt2003]
    exact keyMoment2003 B hB
  · have he : k = (2004 : Fin 2886) := Fin.ext h2004
    subst k
    rw [keyMomentRowsAt2004]
    exact keyMoment2004 B hB
  · have he : k = (2005 : Fin 2886) := Fin.ext h2005
    subst k
    rw [keyMomentRowsAt2005]
    exact keyMoment2005 B hB
  · have he : k = (2006 : Fin 2886) := Fin.ext h2006
    subst k
    rw [keyMomentRowsAt2006]
    exact keyMoment2006 B hB
  · have he : k = (2007 : Fin 2886) := Fin.ext h2007
    subst k
    rw [keyMomentRowsAt2007]
    exact keyMoment2007 B hB
  · have he : k = (2008 : Fin 2886) := Fin.ext h2008
    subst k
    rw [keyMomentRowsAt2008]
    exact keyMoment2008 B hB
  · have he : k = (2009 : Fin 2886) := Fin.ext h2009
    subst k
    rw [keyMomentRowsAt2009]
    exact keyMoment2009 B hB
  · have he : k = (2010 : Fin 2886) := Fin.ext h2010
    subst k
    rw [keyMomentRowsAt2010]
    exact keyMoment2010 B hB
  · have he : k = (2011 : Fin 2886) := Fin.ext h2011
    subst k
    rw [keyMomentRowsAt2011]
    exact keyMoment2011 B hB
  · have he : k = (2012 : Fin 2886) := Fin.ext h2012
    subst k
    rw [keyMomentRowsAt2012]
    exact keyMoment2012 B hB
  · have he : k = (2013 : Fin 2886) := Fin.ext h2013
    subst k
    rw [keyMomentRowsAt2013]
    exact keyMoment2013 B hB
  · have he : k = (2014 : Fin 2886) := Fin.ext h2014
    subst k
    rw [keyMomentRowsAt2014]
    exact keyMoment2014 B hB
  · have he : k = (2015 : Fin 2886) := Fin.ext h2015
    subst k
    rw [keyMomentRowsAt2015]
    exact keyMoment2015 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
